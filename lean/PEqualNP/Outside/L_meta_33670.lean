import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33670

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl wiresStep x

lemma wiresOf_nil (x : List Bool) : wiresOf [] x = x := rfl

lemma wiresOf_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    wiresOf (gs₁ ++ gs₂) x = wiresOf gs₂ (wiresOf gs₁ x) := by
  simp [wiresOf, List.foldl_append]

lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresOf]
  | cons g gs ih =>
    simp only [wiresOf, List.foldl_cons] at ih ⊢
    rw [ih, wiresStep, List.length_append, List.length_singleton]
    simp; omega

lemma wiresOf_getD_lt (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (wiresOf gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [wiresOf, List.foldl_cons] at ih ⊢
    rw [ih (wiresStep x g) (by simp [wiresStep]; omega)]
    simp [wiresStep, List.getD, List.getElem?_append_left hw]

lemma wiresOf_append_getD (gs₁ gs₂ : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs₁.length) :
    (wiresOf (gs₁ ++ gs₂) x).getD w false = (wiresOf gs₁ x).getD w false := by
  rw [wiresOf_append]
  exact wiresOf_getD_lt gs₂ (wiresOf gs₁ x) w (by rw [wiresOf_length]; exact hw)

lemma wiresOf_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wiresOf (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  rw [wiresOf_append, wiresOf, List.foldl_cons, List.foldl_nil, wiresStep]
  have hlen : (wiresOf gs x).length = x.length + gs.length := wiresOf_length gs x
  rw [← hlen]
  simp [List.getD]

structure CState (n_in : ℕ) where
  gates : List Gate

def CState.nw {n_in : ℕ} (s : CState n_in) : ℕ := n_in + s.gates.length

def CState.Valid {n_in : ℕ} (s : CState n_in) : Prop :=
  FanInTwo ⟨s.gates, 0⟩ ∧ ReadsBack n_in ⟨s.gates, 0⟩

def CState.weval {n_in : ℕ} (s : CState n_in) (x : List Bool) (w : ℕ) : Bool :=
  (wiresOf s.gates x).getD w false

def CState.Ext {n_in : ℕ} (s₁ s₂ : CState n_in) : Prop :=
  ∃ extra : List Gate, s₂.gates = s₁.gates ++ extra

lemma CState.ext_refl {n_in : ℕ} (s : CState n_in) : s.Ext s := ⟨[], by simp⟩

lemma CState.ext_trans {n_in : ℕ} {s₁ s₂ s₃ : CState n_in} (h1 : s₁.Ext s₂) (h2 : s₂.Ext s₃) :
    s₁.Ext s₃ := by
  rcases h1 with ⟨e1, he1⟩; rcases h2 with ⟨e2, he2⟩
  exact ⟨e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩

lemma CState.ext_nw {n_in : ℕ} {s₁ s₂ : CState n_in} (h : s₁.Ext s₂) : s₁.nw ≤ s₂.nw := by
  rcases h with ⟨e, he⟩; simp [CState.nw, he]

lemma CState.ext_weval {n_in : ℕ} {s₁ s₂ : CState n_in} (h : s₁.Ext s₂)
    (x : List Bool) (hx : x.length = n_in) (w : ℕ) (hw : w < s₁.nw) :
    s₂.weval x w = s₁.weval x w := by
  rcases h with ⟨e, he⟩
  simp only [CState.weval, he]
  exact wiresOf_append_getD s₁.gates e x w (by rw [hx]; exact hw)

def CState.push {n_in : ℕ} (s : CState n_in) (g : Gate) : CState n_in × ℕ :=
  (⟨s.gates ++ [g]⟩, s.nw)

lemma CState.push_ext {n_in : ℕ} (s : CState n_in) (g : Gate) : s.Ext (s.push g).1 :=
  ⟨[g], rfl⟩

lemma CState.push_len {n_in : ℕ} (s : CState n_in) (g : Gate) :
    (s.push g).1.gates.length = s.gates.length + 1 := by
  simp [CState.push]

lemma CState.push_wire_lt {n_in : ℕ} (s : CState n_in) (g : Gate) :
    (s.push g).2 < (s.push g).1.nw := by
  simp [CState.push, CState.nw]

lemma CState.push_valid {n_in : ℕ} (s : CState n_in) (hs : s.Valid) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < s.nw) : (s.push g).1.Valid := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    simp only [CState.push, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hs.1 g' hg'
    · exact ⟨by rcases hop with h | h | h <;> simp [h], hlen⟩
  · intro j hj i hi
    simp only [CState.push, List.length_append, List.length_singleton] at hj
    by_cases hlt : j < s.gates.length
    · have hga : gateAt ⟨s.gates ++ [g], 0⟩ j = gateAt ⟨s.gates, 0⟩ j := by
        simp [gateAt, List.getD, List.getElem?_append_left hlt]
      simp only [CState.push] at hi
      rw [hga] at hi
      exact hs.2 j hlt i hi
    · have hj_eq : j = s.gates.length := by omega
      subst hj_eq
      have hga : gateAt ⟨s.gates ++ [g], 0⟩ s.gates.length = g := by
        simp [gateAt, List.getD]
      simp only [CState.push] at hi
      rw [hga] at hi
      exact hin i hi

lemma CState.push_weval {n_in : ℕ} (s : CState n_in) (g : Gate) (x : List Bool)
    (hx : x.length = n_in) :
    (s.push g).1.weval x (s.push g).2 = g.op.eval (g.inputs.map fun i => s.weval x i) := by
  subst hx
  simp only [CState.push, CState.weval, CState.nw]
  exact wiresOf_snoc_last s.gates g x

def mkConst {n_in : ℕ} (s : CState n_in) (b : Bool) : CState n_in × ℕ :=
  s.push ⟨if b then .and else .or, []⟩

lemma mkConst_spec {n_in : ℕ} (s : CState n_in) (hs : s.Valid) (b : Bool) :
    let r := mkConst s b
    s.Ext r.1 ∧ r.1.Valid ∧ r.2 < r.1.nw ∧ r.1.gates.length = s.gates.length + 1 ∧
    ∀ x : List Bool, x.length = n_in → r.1.weval x r.2 = b := by
  refine ⟨CState.push_ext _ _, CState.push_valid s hs _ (by cases b <;> simp) (by simp) (by simp),
    CState.push_wire_lt _ _, CState.push_len _ _, ?_⟩
  intro x hx
  simp only [mkConst]
  rw [CState.push_weval s _ x hx]
  cases b <;> simp [GateOp.eval]

def mkAnd {n_in : ℕ} (s : CState n_in) (a b : ℕ) : CState n_in × ℕ :=
  s.push ⟨.and, [a, b]⟩

lemma mkAnd_spec {n_in : ℕ} (s : CState n_in) (hs : s.Valid) (a b : ℕ)
    (ha : a < s.nw) (hb : b < s.nw) :
    let r := mkAnd s a b
    s.Ext r.1 ∧ r.1.Valid ∧ r.2 < r.1.nw ∧ r.1.gates.length = s.gates.length + 1 ∧
    ∀ x : List Bool, x.length = n_in → r.1.weval x r.2 = (s.weval x a && s.weval x b) := by
  refine ⟨CState.push_ext _ _, CState.push_valid s hs _ (by simp) (by simp)
      (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    CState.push_wire_lt _ _, CState.push_len _ _, ?_⟩
  intro x hx
  simp only [mkAnd]
  rw [CState.push_weval s _ x hx]
  simp [GateOp.eval]

def mkOr {n_in : ℕ} (s : CState n_in) (a b : ℕ) : CState n_in × ℕ :=
  s.push ⟨.or, [a, b]⟩

lemma mkOr_spec {n_in : ℕ} (s : CState n_in) (hs : s.Valid) (a b : ℕ)
    (ha : a < s.nw) (hb : b < s.nw) :
    let r := mkOr s a b
    s.Ext r.1 ∧ r.1.Valid ∧ r.2 < r.1.nw ∧ r.1.gates.length = s.gates.length + 1 ∧
    ∀ x : List Bool, x.length = n_in → r.1.weval x r.2 = (s.weval x a || s.weval x b) := by
  refine ⟨CState.push_ext _ _, CState.push_valid s hs _ (by simp) (by simp)
      (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    CState.push_wire_lt _ _, CState.push_len _ _, ?_⟩
  intro x hx
  simp only [mkOr]
  rw [CState.push_weval s _ x hx]
  simp [GateOp.eval]

def mkNot {n_in : ℕ} (s : CState n_in) (a : ℕ) : CState n_in × ℕ :=
  s.push ⟨.not, [a]⟩

lemma mkNot_spec {n_in : ℕ} (s : CState n_in) (hs : s.Valid) (a : ℕ) (ha : a < s.nw) :
    let r := mkNot s a
    s.Ext r.1 ∧ r.1.Valid ∧ r.2 < r.1.nw ∧ r.1.gates.length = s.gates.length + 1 ∧
    ∀ x : List Bool, x.length = n_in → r.1.weval x r.2 = !(s.weval x a) := by
  refine ⟨CState.push_ext _ _, CState.push_valid s hs _ (by simp) (by simp)
      (by intro i hi; simp at hi; subst hi; exact ha),
    CState.push_wire_lt _ _, CState.push_len _ _, ?_⟩
  intro x hx
  simp only [mkNot]
  rw [CState.push_weval s _ x hx]
  simp [GateOp.eval]

def mkXor {n_in : ℕ} (s : CState n_in) (a b : ℕ) : CState n_in × ℕ :=
  let (s1, na) := mkNot s a
  let (s2, nb) := mkNot s1 b
  let (s3, w1) := mkAnd s2 a nb
  let (s4, w2) := mkAnd s3 na b
  mkOr s4 w1 w2

lemma mkXor_spec {n_in : ℕ} (s : CState n_in) (hs : s.Valid) (a b : ℕ)
    (ha : a < s.nw) (hb : b < s.nw) :
    let r := mkXor s a b
    s.Ext r.1 ∧ r.1.Valid ∧ r.2 < r.1.nw ∧ r.1.gates.length = s.gates.length + 5 ∧
    ∀ x : List Bool, x.length = n_in → r.1.weval x r.2 = xor (s.weval x a) (s.weval x b) := by
  dsimp only [mkXor]
  have h1 := mkNot_spec s hs a ha
  set s1 := (mkNot s a).1; set na := (mkNot s a).2
  have h2 := mkNot_spec s1 h1.2.1 b (lt_of_lt_of_le hb (CState.ext_nw h1.1))
  set s2 := (mkNot s1 b).1; set nb := (mkNot s1 b).2
  have h12 : s.Ext s2 := CState.ext_trans h1.1 h2.1
  have h3 := mkAnd_spec s2 h2.2.1 a nb (lt_of_lt_of_le ha (CState.ext_nw h12)) h2.2.2.1
  set s3 := (mkAnd s2 a nb).1; set w1 := (mkAnd s2 a nb).2
  have h13 : s1.Ext s3 := CState.ext_trans h2.1 h3.1
  have h03 : s.Ext s3 := CState.ext_trans h1.1 h13
  have h4 := mkAnd_spec s3 h3.2.1 na b (lt_of_lt_of_le h1.2.2.1 (CState.ext_nw h13))
    (lt_of_lt_of_le hb (CState.ext_nw h03))
  set s4 := (mkAnd s3 na b).1; set w2 := (mkAnd s3 na b).2
  have h5 := mkOr_spec s4 h4.2.1 w1 w2 (lt_of_lt_of_le h3.2.2.1 (CState.ext_nw h4.1)) h4.2.2.1
  refine ⟨CState.ext_trans h03 (CState.ext_trans h4.1 h5.1), h5.2.1, h5.2.2.1,
    by have := h1.2.2.2.1; have := h2.2.2.2.1; have := h3.2.2.2.1; have := h4.2.2.2.1; have := h5.2.2.2.1
       dsimp only [s1, s2, s3, s4] at *; omega, ?_⟩
  intro x hx
  rw [h5.2.2.2.2 x hx, CState.ext_weval h4.1 x hx w1 h3.2.2.1,
    h3.2.2.2.2 x hx, h4.2.2.2.2 x hx,
    CState.ext_weval h12 x hx a ha, h2.2.2.2.2 x hx,
    CState.ext_weval h1.1 x hx b hb, CState.ext_weval h13 x hx na h1.2.2.1,
    h1.2.2.2.2 x hx, CState.ext_weval h03 x hx b hb]
  cases s.weval x a <;> cases s.weval x b <;> rfl

def mkIte {n_in : ℕ} (s : CState n_in) (c a b : ℕ) : CState n_in × ℕ :=
  let (s1, nc) := mkNot s c
  let (s2, w1) := mkAnd s1 c a
  let (s3, w2) := mkAnd s2 nc b
  mkOr s3 w1 w2

lemma mkIte_spec {n_in : ℕ} (s : CState n_in) (hs : s.Valid) (c a b : ℕ)
    (hc : c < s.nw) (ha : a < s.nw) (hb : b < s.nw) :
    let r := mkIte s c a b
    s.Ext r.1 ∧ r.1.Valid ∧ r.2 < r.1.nw ∧ r.1.gates.length = s.gates.length + 4 ∧
    ∀ x : List Bool, x.length = n_in →
      r.1.weval x r.2 = if s.weval x c then s.weval x a else s.weval x b := by
  dsimp only [mkIte]
  have h1 := mkNot_spec s hs c hc
  set s1 := (mkNot s c).1; set nc := (mkNot s c).2
  have h2 := mkAnd_spec s1 h1.2.1 c a (lt_of_lt_of_le hc (CState.ext_nw h1.1))
    (lt_of_lt_of_le ha (CState.ext_nw h1.1))
  set s2 := (mkAnd s1 c a).1; set w1 := (mkAnd s1 c a).2
  have h02 : s.Ext s2 := CState.ext_trans h1.1 h2.1
  have h3 := mkAnd_spec s2 h2.2.1 nc b (lt_of_lt_of_le h1.2.2.1 (CState.ext_nw h2.1))
    (lt_of_lt_of_le hb (CState.ext_nw h02))
  set s3 := (mkAnd s2 nc b).1; set w2 := (mkAnd s2 nc b).2
  have h4 := mkOr_spec s3 h3.2.1 w1 w2 (lt_of_lt_of_le h2.2.2.1 (CState.ext_nw h3.1)) h3.2.2.1
  refine ⟨CState.ext_trans h02 (CState.ext_trans h3.1 h4.1), h4.2.1, h4.2.2.1,
    by have := h1.2.2.2.1; have := h2.2.2.2.1; have := h3.2.2.2.1; have := h4.2.2.2.1
       dsimp only [s1, s2, s3] at *; omega, ?_⟩
  intro x hx
  rw [h4.2.2.2.2 x hx, CState.ext_weval h3.1 x hx w1 h2.2.2.1,
    h2.2.2.2.2 x hx, h3.2.2.2.2 x hx,
    CState.ext_weval h1.1 x hx c hc, CState.ext_weval h1.1 x hx a ha,
    CState.ext_weval h2.1 x hx nc h1.2.2.1, h1.2.2.2.2 x hx,
    CState.ext_weval h02 x hx b hb]
  cases s.weval x c <;> cases s.weval x a <;> cases s.weval x b <;> rfl

def mkEq {n_in : ℕ} (s : CState n_in) (a b : ℕ) : CState n_in × ℕ :=
  let (s1, w) := mkXor s a b
  mkNot s1 w

lemma mkEq_spec {n_in : ℕ} (s : CState n_in) (hs : s.Valid) (a b : ℕ)
    (ha : a < s.nw) (hb : b < s.nw) :
    let r := mkEq s a b
    s.Ext r.1 ∧ r.1.Valid ∧ r.2 < r.1.nw ∧ r.1.gates.length = s.gates.length + 6 ∧
    ∀ x : List Bool, x.length = n_in → r.1.weval x r.2 = decide (s.weval x a = s.weval x b) := by
  dsimp only [mkEq]
  have h1 := mkXor_spec s hs a b ha hb
  have h2 := mkNot_spec _ h1.2.1 _ h1.2.2.1
  refine ⟨CState.ext_trans h1.1 h2.1, h2.2.1, h2.2.2.1, by omega, ?_⟩
  intro x hx
  rw [h2.2.2.2.2 x hx, h1.2.2.2.2 x hx]
  cases s.weval x a <;> cases s.weval x b <;> rfl

abbrev BVec (L : ℕ) := Fin L → ℕ

def bvVal {n_in L : ℕ} (s : CState n_in) (x : List Bool) (v : BVec L) : ℕ :=
  ∑ i : Fin L, if s.weval x (v i) then 2 ^ i.val else 0

lemma bvVal_lt {n_in L : ℕ} (s : CState n_in) (x : List Bool) (v : BVec L) :
    bvVal s x v < 2 ^ L := by
  induction L with
  | zero => simp [bvVal]
  | succ m ih =>
    unfold bvVal
    rw [Fin.sum_univ_castSucc]
    have h1 : (∑ i : Fin m, if s.weval x (v i.castSucc) = true then 2 ^ i.val else 0) < 2 ^ m :=
      ih (fun i => v i.castSucc)
    have h2 : (if s.weval x (v (Fin.last m)) = true then 2 ^ m else 0) ≤ 2 ^ m := by
      split_ifs <;> omega
    have h3 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
    simp only [Fin.val_castSucc, Fin.val_last] at h1 ⊢
    omega

lemma bvVal_testBit {n_in L : ℕ} (s : CState n_in) (x : List Bool) (v : BVec L) (i : Fin L) :
    (bvVal s x v).testBit i.val = s.weval x (v i) := by
  induction L with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    unfold bvVal
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    set lo := ∑ j : Fin m, if s.weval x (v j.castSucc) = true then 2 ^ j.val else 0
    have hlo : lo < 2 ^ m := bvVal_lt s x (fun j => v j.castSucc)
    by_cases hlast : i = Fin.last m
    · subst hlast
      simp only [Fin.val_last]
      cases hb : s.weval x (v (Fin.last m))
      · simp [Nat.testBit_lt_two_pow hlo]
      · simp only [↓reduceIte]
        rw [Nat.add_comm lo, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlo]; rfl
    · have hi : i.val < m := by
        have := i.isLt
        have : i.val ≠ m := fun h => hlast (Fin.ext h)
        omega
      let i' : Fin m := ⟨i.val, hi⟩
      have hi'_eq : i'.castSucc = i := Fin.ext rfl
      cases hb : s.weval x (v (Fin.last m))
      · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        have := ih (fun j => v j.castSucc) i'
        simpa [bvVal, lo, hi'_eq] using this
      · simp only [↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hi]
        have := ih (fun j => v j.castSucc) i'
        simpa [bvVal, lo, hi'_eq] using this

lemma bvVal_ext {n_in L : ℕ} {s₁ s₂ : CState n_in} (h : s₁.Ext s₂)
    (x : List Bool) (hx : x.length = n_in) (v : BVec L) (hv : ∀ i, v i < s₁.nw) :
    bvVal s₂ x v = bvVal s₁ x v := by
  unfold bvVal
  apply Finset.sum_congr rfl
  intro i _
  rw [CState.ext_weval h x hx (v i) (hv i)]

def mkBvConst {n_in : ℕ} (s : CState n_in) (L c : ℕ) : CState n_in × BVec L :=
  let (s0, w0) := mkConst s false
  let (s1, w1) := mkConst s0 true
  (s1, fun i => if c.testBit i.val then w1 else w0)

lemma mkBvConst_spec {n_in : ℕ} (s : CState n_in) (hs : s.Valid) (L c : ℕ) :
    let r := mkBvConst s L c
    s.Ext r.1 ∧ r.1.Valid ∧ (∀ i, r.2 i < r.1.nw) ∧ r.1.gates.length = s.gates.length + 2 ∧
    ∀ x : List Bool, x.length = n_in → bvVal r.1 x r.2 = c % 2 ^ L := by
  dsimp only [mkBvConst]
  have h0 := mkConst_spec s hs false
  set s0 := (mkConst s false).1; set w0 := (mkConst s false).2
  have h1 := mkConst_spec s0 h0.2.1 true
  set s1 := (mkConst s0 true).1; set w1 := (mkConst s0 true).2
  refine ⟨CState.ext_trans h0.1 h1.1, h1.2.1, ?_,
    by have := h0.2.2.2.1; have := h1.2.2.2.1; dsimp only [s0, s1] at *; omega, ?_⟩
  · intro i; split_ifs
    · exact h1.2.2.1
    · exact lt_of_lt_of_le h0.2.2.1 (CState.ext_nw h1.1)
  · intro x hx
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < L
    · let jf : Fin L := ⟨j, hj⟩
      have htb := bvVal_testBit s1 x (fun i : Fin L => if c.testBit i.val then w1 else w0) jf
      rw [htb, Nat.testBit_mod_two_pow]
      simp only [jf, hj, decide_true, Bool.true_and]
      cases hc : c.testBit j
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [CState.ext_weval h1.1 x hx w0 h0.2.2.1]; exact h0.2.2.2.2 x hx
      · simp only [↓reduceIte]; exact h1.2.2.2.2 x hx
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (bvVal_lt s1 x _) (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_mod_two_pow]
      simp [hj]

def mkFullAdd {n_in : ℕ} (s : CState n_in) (a b cin : ℕ) : CState n_in × ℕ × ℕ :=
  let (s1, axb) := mkXor s a b
  let (s2, sum) := mkXor s1 axb cin
  let (s3, ab) := mkAnd s2 a b
  let (s4, caxb) := mkAnd s3 cin axb
  let (s5, cout) := mkOr s4 ab caxb
  (s5, sum, cout)

lemma mkFullAdd_spec {n_in : ℕ} (s : CState n_in) (hs : s.Valid) (a b cin : ℕ)
    (ha : a < s.nw) (hb : b < s.nw) (hc : cin < s.nw) :
    let r := mkFullAdd s a b cin
    s.Ext r.1 ∧ r.1.Valid ∧ r.2.1 < r.1.nw ∧ r.2.2 < r.1.nw ∧
    r.1.gates.length = s.gates.length + 13 ∧
    ∀ x : List Bool, x.length = n_in →
      (r.1.weval x r.2.1).toNat + 2 * (r.1.weval x r.2.2).toNat =
        (s.weval x a).toNat + (s.weval x b).toNat + (s.weval x cin).toNat := by
  dsimp only [mkFullAdd]
  have h1 := mkXor_spec s hs a b ha hb
  set s1 := (mkXor s a b).1; set axb := (mkXor s a b).2
  have h2 := mkXor_spec s1 h1.2.1 axb cin h1.2.2.1 (lt_of_lt_of_le hc (CState.ext_nw h1.1))
  set s2 := (mkXor s1 axb cin).1; set sum := (mkXor s1 axb cin).2
  have h02 : s.Ext s2 := CState.ext_trans h1.1 h2.1
  have h3 := mkAnd_spec s2 h2.2.1 a b (lt_of_lt_of_le ha (CState.ext_nw h02))
    (lt_of_lt_of_le hb (CState.ext_nw h02))
  set s3 := (mkAnd s2 a b).1; set ab := (mkAnd s2 a b).2
  have h03 : s.Ext s3 := CState.ext_trans h02 h3.1
  have h13 : s1.Ext s3 := CState.ext_trans h2.1 h3.1
  have h4 := mkAnd_spec s3 h3.2.1 cin axb (lt_of_lt_of_le hc (CState.ext_nw h03))
    (lt_of_lt_of_le h1.2.2.1 (CState.ext_nw h13))
  set s4 := (mkAnd s3 cin axb).1; set caxb := (mkAnd s3 cin axb).2
  have h5 := mkOr_spec s4 h4.2.1 ab caxb (lt_of_lt_of_le h3.2.2.1 (CState.ext_nw h4.1)) h4.2.2.1
  set s5 := (mkOr s4 ab caxb).1; set cout := (mkOr s4 ab caxb).2
  have h25 : s2.Ext s5 := CState.ext_trans h3.1 (CState.ext_trans h4.1 h5.1)
  refine ⟨CState.ext_trans h03 (CState.ext_trans h4.1 h5.1), h5.2.1,
    lt_of_lt_of_le h2.2.2.1 (CState.ext_nw h25), h5.2.2.1,
    by have := h1.2.2.2.1; have := h2.2.2.2.1; have := h3.2.2.2.1; have := h4.2.2.2.1; have := h5.2.2.2.1
       dsimp only [s1, s2, s3, s4, s5] at *; omega, ?_⟩
  intro x hx
  rw [CState.ext_weval h25 x hx sum h2.2.2.1, h2.2.2.2.2 x hx,
    h5.2.2.2.2 x hx, CState.ext_weval h4.1 x hx ab h3.2.2.1,
    h3.2.2.2.2 x hx, h4.2.2.2.2 x hx,
    CState.ext_weval h02 x hx a ha, CState.ext_weval h02 x hx b hb,
    CState.ext_weval h03 x hx cin hc, CState.ext_weval h13 x hx axb h1.2.2.1,
    h1.2.2.2.2 x hx, CState.ext_weval h1.1 x hx cin hc]
  cases s.weval x a <;> cases s.weval x b <;> cases s.weval x cin <;> rfl

def mkBvAddAux {n_in : ℕ} : (L : ℕ) → CState n_in → BVec L → BVec L → ℕ → CState n_in × BVec L × ℕ
  | 0, s, _, _, cin => (s, Fin.elim0, cin)
  | m + 1, s, a, b, cin =>
    let (s1, v_lo, c1) := mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin
    let (s2, sbit, c2) := mkFullAdd s1 (a (Fin.last m)) (b (Fin.last m)) c1
    (s2, Fin.snoc v_lo sbit, c2)

lemma mkBvAddAux_spec {n_in : ℕ} (L : ℕ) (s : CState n_in) (hs : s.Valid)
    (a b : BVec L) (cin : ℕ)
    (ha : ∀ i, a i < s.nw) (hb : ∀ i, b i < s.nw) (hc : cin < s.nw) :
    let r := mkBvAddAux L s a b cin
    s.Ext r.1 ∧ r.1.Valid ∧ (∀ i, r.2.1 i < r.1.nw) ∧ r.2.2 < r.1.nw ∧
    r.1.gates.length = s.gates.length + 13 * L ∧
    ∀ x : List Bool, x.length = n_in →
      bvVal r.1 x r.2.1 + 2 ^ L * (r.1.weval x r.2.2).toNat =
        bvVal s x a + bvVal s x b + (s.weval x cin).toNat := by
  induction L generalizing s cin with
  | zero =>
    refine ⟨CState.ext_refl s, hs, fun i => Fin.elim0 i, hc, by simp [mkBvAddAux], ?_⟩
    intro x _; simp [mkBvAddAux, bvVal]
  | succ m ih =>
    dsimp only [mkBvAddAux]
    have h1 := ih s hs (fun i => a i.castSucc) (fun i => b i.castSucc) cin
      (fun i => ha _) (fun i => hb _) hc
    set s1 := (mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).1
    set vlo := (mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).2.1
    set c1 := (mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).2.2
    have h2 := mkFullAdd_spec s1 h1.2.1 (a (Fin.last m)) (b (Fin.last m)) c1
      (lt_of_lt_of_le (ha _) (CState.ext_nw h1.1))
      (lt_of_lt_of_le (hb _) (CState.ext_nw h1.1)) h1.2.2.2.1
    set s2 := (mkFullAdd s1 (a (Fin.last m)) (b (Fin.last m)) c1).1
    set sbit := (mkFullAdd s1 (a (Fin.last m)) (b (Fin.last m)) c1).2.1
    set c2 := (mkFullAdd s1 (a (Fin.last m)) (b (Fin.last m)) c1).2.2
    refine ⟨CState.ext_trans h1.1 h2.1, h2.2.1, ?_, h2.2.2.2.1,
      by have := h1.2.2.2.2.1; have := h2.2.2.2.2.1; dsimp only [s1, s2] at *; omega, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last]; exact h2.2.2.1
      · intro j; rw [Fin.snoc_castSucc]; exact lt_of_lt_of_le (h1.2.2.1 j) (CState.ext_nw h2.1)
    · intro x hx
      have hlo_eq : bvVal s2 x (Fin.snoc vlo sbit) =
          bvVal s1 x vlo + 2 ^ m * (s2.weval x sbit).toNat := by
        unfold bvVal
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        have hsum : ∑ i : Fin m, (if s2.weval x (vlo i) = true then 2 ^ i.val else 0) =
            ∑ i : Fin m, (if s1.weval x (vlo i) = true then 2 ^ i.val else 0) :=
          Finset.sum_congr rfl (fun i _ => by rw [CState.ext_weval h2.1 x hx (vlo i) (h1.2.2.1 i)])
        rw [hsum]
        cases s2.weval x sbit <;> simp
      have ha_eq : bvVal s x a = bvVal s x (fun i => a i.castSucc) + 2 ^ m * (s.weval x (a (Fin.last m))).toNat := by
        unfold bvVal; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
        cases s.weval x (a (Fin.last m)) <;> simp
      have hb_eq : bvVal s x b = bvVal s x (fun i => b i.castSucc) + 2 ^ m * (s.weval x (b (Fin.last m))).toNat := by
        unfold bvVal; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
        cases s.weval x (b (Fin.last m)) <;> simp
      have hf := h2.2.2.2.2.2 x hx
      rw [CState.ext_weval h1.1 x hx (a (Fin.last m)) (ha _),
          CState.ext_weval h1.1 x hx (b (Fin.last m)) (hb _)] at hf
      have hih := h1.2.2.2.2.2 x hx
      have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
      rw [hlo_eq, ha_eq, hb_eq, hpow]
      dsimp only [s1, vlo, c1, s2, sbit, c2] at *
      have hf' : 2 ^ m * (((mkFullAdd (mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).1
            (a (Fin.last m)) (b (Fin.last m))
            (mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).2.2).1.weval x
            (mkFullAdd (mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).1
              (a (Fin.last m)) (b (Fin.last m))
              (mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).2.2).2.1).toNat +
          2 * ((mkFullAdd (mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).1
            (a (Fin.last m)) (b (Fin.last m))
            (mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).2.2).1.weval x
            (mkFullAdd (mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).1
              (a (Fin.last m)) (b (Fin.last m))
              (mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).2.2).2.2).toNat) =
          2 ^ m * ((s.weval x (a (Fin.last m))).toNat + (s.weval x (b (Fin.last m))).toNat +
            ((mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).1.weval x
              (mkBvAddAux m s (fun i => a i.castSucc) (fun i => b i.castSucc) cin).2.2).toNat) :=
        congrArg (2 ^ m * ·) hf
      linarith

def mkBvAdd {n_in L : ℕ} (s : CState n_in) (a b : BVec L) : CState n_in × BVec L :=
  let (s0, z) := mkConst s false
  let (s1, v, _) := mkBvAddAux L s0 a b z
  (s1, v)

lemma mkBvAdd_spec {n_in L : ℕ} (s : CState n_in) (hs : s.Valid) (a b : BVec L)
    (ha : ∀ i, a i < s.nw) (hb : ∀ i, b i < s.nw) :
    let r := mkBvAdd s a b
    s.Ext r.1 ∧ r.1.Valid ∧ (∀ i, r.2 i < r.1.nw) ∧ r.1.gates.length = s.gates.length + 13 * L + 1 ∧
    ∀ x : List Bool, x.length = n_in → bvVal r.1 x r.2 = (bvVal s x a + bvVal s x b) % 2 ^ L := by
  dsimp only [mkBvAdd]
  have h0 := mkConst_spec s hs false
  have h1 := mkBvAddAux_spec L _ h0.2.1 a b _
    (fun i => lt_of_lt_of_le (ha i) (CState.ext_nw h0.1))
    (fun i => lt_of_lt_of_le (hb i) (CState.ext_nw h0.1)) h0.2.2.1
  refine ⟨CState.ext_trans h0.1 h1.1, h1.2.1, h1.2.2.1, by omega, ?_⟩
  intro x hx
  have heq := h1.2.2.2.2.2 x hx
  rw [h0.2.2.2.2 x hx, bvVal_ext h0.1 x hx a ha, bvVal_ext h0.1 x hx b hb] at heq
  simp only [Bool.toNat_false, add_zero] at heq
  have hlt := bvVal_lt (mkBvAddAux L (mkConst s false).1 a b (mkConst s false).2).1 x
    (mkBvAddAux L (mkConst s false).1 a b (mkConst s false).2).2.1
  rw [← heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

def mkBvNot {n_in : ℕ} : (L : ℕ) → CState n_in → BVec L → CState n_in × BVec L
  | 0, s, _ => (s, Fin.elim0)
  | m + 1, s, a =>
    let (s1, vlo) := mkBvNot m s (fun i => a i.castSucc)
    let (s2, hi) := mkNot s1 (a (Fin.last m))
    (s2, Fin.snoc vlo hi)

lemma mkBvNot_spec {n_in : ℕ} (L : ℕ) (s : CState n_in) (hs : s.Valid) (a : BVec L)
    (ha : ∀ i, a i < s.nw) :
    let r := mkBvNot L s a
    s.Ext r.1 ∧ r.1.Valid ∧ (∀ i, r.2 i < r.1.nw) ∧ r.1.gates.length = s.gates.length + L ∧
    ∀ x : List Bool, x.length = n_in → bvVal r.1 x r.2 + bvVal s x a + 1 = 2 ^ L := by
  induction L generalizing s with
  | zero =>
    refine ⟨CState.ext_refl s, hs, fun i => Fin.elim0 i, by simp [mkBvNot], ?_⟩
    intro x _; simp [mkBvNot, bvVal]
  | succ m ih =>
    dsimp only [mkBvNot]
    have h1 := ih s hs (fun i => a i.castSucc) (fun i => ha _)
    set s1 := (mkBvNot m s (fun i => a i.castSucc)).1
    set vlo := (mkBvNot m s (fun i => a i.castSucc)).2
    have h2 := mkNot_spec s1 h1.2.1 (a (Fin.last m)) (lt_of_lt_of_le (ha _) (CState.ext_nw h1.1))
    set s2 := (mkNot s1 (a (Fin.last m))).1; set hi := (mkNot s1 (a (Fin.last m))).2
    refine ⟨CState.ext_trans h1.1 h2.1, h2.2.1, ?_,
      by have := h1.2.2.2.1; have := h2.2.2.2.1; dsimp only [s1, s2] at *; omega, ?_⟩
    · intro i
      refine Fin.lastCases (by rw [Fin.snoc_last]; exact h2.2.2.1)
        (fun j => by rw [Fin.snoc_castSucc]; exact lt_of_lt_of_le (h1.2.2.1 j) (CState.ext_nw h2.1)) i
    · intro x hx
      have hlo_eq : bvVal s2 x (Fin.snoc vlo hi) = bvVal s1 x vlo + 2 ^ m * (s2.weval x hi).toNat := by
        unfold bvVal; rw [Fin.sum_univ_castSucc]; simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        rw [Finset.sum_congr rfl (fun i _ => by rw [CState.ext_weval h2.1 x hx (vlo i) (h1.2.2.1 i)])]
        cases s2.weval x hi <;> simp
      have ha_eq : bvVal s x a = bvVal s x (fun i => a i.castSucc) + 2 ^ m * (s.weval x (a (Fin.last m))).toNat := by
        unfold bvVal; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
        cases s.weval x (a (Fin.last m)) <;> simp
      have hhi : (s2.weval x hi).toNat + (s.weval x (a (Fin.last m))).toNat = 1 := by
        rw [h2.2.2.2.2 x hx, CState.ext_weval h1.1 x hx (a (Fin.last m)) (ha _)]
        cases s.weval x (a (Fin.last m)) <;> rfl
      have hih := h1.2.2.2.2 x hx
      have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
      rw [hlo_eq, ha_eq, hpow]
      nlinarith

def mkBvSub {n_in L : ℕ} (s : CState n_in) (a b : BVec L) : CState n_in × BVec L :=
  let (s1, nb) := mkBvNot L s b
  let (s2, one) := mkConst s1 true
  let (s3, v, _) := mkBvAddAux L s2 a nb one
  (s3, v)

lemma mkBvSub_spec {n_in L : ℕ} (s : CState n_in) (hs : s.Valid) (a b : BVec L)
    (ha : ∀ i, a i < s.nw) (hb : ∀ i, b i < s.nw) :
    let r := mkBvSub s a b
    s.Ext r.1 ∧ r.1.Valid ∧ (∀ i, r.2 i < r.1.nw) ∧ r.1.gates.length = s.gates.length + 14 * L + 1 ∧
    ∀ x : List Bool, x.length = n_in → bvVal s x b ≤ bvVal s x a →
      bvVal r.1 x r.2 = bvVal s x a - bvVal s x b := by
  dsimp only [mkBvSub]
  have h1 := mkBvNot_spec L s hs b hb
  have h2 := mkConst_spec _ h1.2.1 true
  have h02 : s.Ext (mkConst (mkBvNot L s b).1 true).1 := CState.ext_trans h1.1 h2.1
  have h3 := mkBvAddAux_spec L _ h2.2.1 a (mkBvNot L s b).2 _
    (fun i => lt_of_lt_of_le (ha i) (CState.ext_nw h02))
    (fun i => lt_of_lt_of_le (h1.2.2.1 i) (CState.ext_nw h2.1)) h2.2.2.1
  refine ⟨CState.ext_trans h02 h3.1, h3.2.1, h3.2.2.1, by omega, ?_⟩
  intro x hx hle
  have heq := h3.2.2.2.2.2 x hx
  rw [h2.2.2.2.2 x hx, bvVal_ext h02 x hx a ha, bvVal_ext h2.1 x hx _ h1.2.2.1] at heq
  simp only [Bool.toNat_true] at heq
  have hnot := h1.2.2.2.2 x hx
  have hlt_a := bvVal_lt s x a
  set r3 := mkBvAddAux L (mkConst (mkBvNot L s b).1 true).1 a (mkBvNot L s b).2 (mkConst (mkBvNot L s b).1 true).2
  have hlt_r := bvVal_lt r3.1 x r3.2.1
  cases hcout : r3.1.weval x r3.2.2
  · dsimp only [r3] at *
    rw [hcout] at heq; simp only [Bool.toNat_false, mul_zero, add_zero] at heq; omega
  · dsimp only [r3] at *
    rw [hcout] at heq; simp only [Bool.toNat_true, mul_one] at heq
    have hsum : bvVal (mkBvAddAux L (mkConst (mkBvNot L s b).1 true).1 a (mkBvNot L s b).2 (mkConst (mkBvNot L s b).1 true).2).1
      x (mkBvAddAux L (mkConst (mkBvNot L s b).1 true).1 a (mkBvNot L s b).2 (mkConst (mkBvNot L s b).1 true).2).2.1 +
      bvVal s x b = bvVal s x a := by linarith
    exact Nat.eq_sub_of_add_eq hsum

def mkBvLtAux {n_in : ℕ} : (L : ℕ) → CState n_in → BVec L → BVec L → CState n_in × ℕ
  | 0, s, _, _ => mkConst s false
  | m + 1, s, a, b =>
    let (s1, lt_lo) := mkBvLtAux m s (fun i => a i.castSucc) (fun i => b i.castSucc)
    let (s2, na) := mkNot s1 (a (Fin.last m))
    let (s3, lt_hi) := mkAnd s2 na (b (Fin.last m))
    let (s4, eq_hi) := mkEq s3 (a (Fin.last m)) (b (Fin.last m))
    let (s5, mid) := mkAnd s4 eq_hi lt_lo
    mkOr s5 lt_hi mid

lemma mkBvLt_spec {n_in : ℕ} (L : ℕ) (s : CState n_in) (hs : s.Valid) (a b : BVec L)
    (ha : ∀ i, a i < s.nw) (hb : ∀ i, b i < s.nw) :
    let r := mkBvLtAux L s a b
    s.Ext r.1 ∧ r.1.Valid ∧ r.2 < r.1.nw ∧ r.1.gates.length = s.gates.length + 10 * L + 1 ∧
    ∀ x : List Bool, x.length = n_in → r.1.weval x r.2 = decide (bvVal s x a < bvVal s x b) := by
  induction L generalizing s with
  | zero =>
    have h0 := mkConst_spec s hs false
    refine ⟨h0.1, h0.2.1, h0.2.2.1, by simp [mkBvLtAux, h0.2.2.2.1], ?_⟩
    intro x hx; simp [mkBvLtAux, h0.2.2.2.2 x hx, bvVal]
  | succ m ih =>
    dsimp only [mkBvLtAux]
    have h1 := ih s hs (fun i => a i.castSucc) (fun i => b i.castSucc) (fun i => ha _) (fun i => hb _)
    set s1 := (mkBvLtAux m s (fun i => a i.castSucc) (fun i => b i.castSucc)).1
    set lt_lo := (mkBvLtAux m s (fun i => a i.castSucc) (fun i => b i.castSucc)).2
    have h2 := mkNot_spec s1 h1.2.1 (a (Fin.last m)) (lt_of_lt_of_le (ha _) (CState.ext_nw h1.1))
    set s2 := (mkNot s1 (a (Fin.last m))).1; set na := (mkNot s1 (a (Fin.last m))).2
    have h02 : s.Ext s2 := CState.ext_trans h1.1 h2.1
    have h3 := mkAnd_spec s2 h2.2.1 na (b (Fin.last m)) h2.2.2.1 (lt_of_lt_of_le (hb _) (CState.ext_nw h02))
    set s3 := (mkAnd s2 na (b (Fin.last m))).1; set lt_hi := (mkAnd s2 na (b (Fin.last m))).2
    have h03 : s.Ext s3 := CState.ext_trans h02 h3.1
    have h4 := mkEq_spec s3 h3.2.1 (a (Fin.last m)) (b (Fin.last m))
      (lt_of_lt_of_le (ha _) (CState.ext_nw h03)) (lt_of_lt_of_le (hb _) (CState.ext_nw h03))
    set s4 := (mkEq s3 (a (Fin.last m)) (b (Fin.last m))).1
    set eq_hi := (mkEq s3 (a (Fin.last m)) (b (Fin.last m))).2
    have h14 : s1.Ext s4 := CState.ext_trans h2.1 (CState.ext_trans h3.1 h4.1)
    have h5 := mkAnd_spec s4 h4.2.1 eq_hi lt_lo h4.2.2.1 (lt_of_lt_of_le h1.2.2.1 (CState.ext_nw h14))
    set s5 := (mkAnd s4 eq_hi lt_lo).1; set mid := (mkAnd s4 eq_hi lt_lo).2
    have h35 : s3.Ext s5 := CState.ext_trans h4.1 h5.1
    have h6 := mkOr_spec s5 h5.2.1 lt_hi mid (lt_of_lt_of_le h3.2.2.1 (CState.ext_nw h35)) h5.2.2.1
    refine ⟨CState.ext_trans h03 (CState.ext_trans h35 h6.1), h6.2.1, h6.2.2.1,
      by have := h1.2.2.2.1; have := h2.2.2.2.1; have := h3.2.2.2.1; have := h4.2.2.2.1
         have := h5.2.2.2.1; have := h6.2.2.2.1
         dsimp only [s1, s2, s3, s4, s5] at *; omega, ?_⟩
    intro x hx
    rw [h6.2.2.2.2 x hx, CState.ext_weval h35 x hx lt_hi h3.2.2.1,
      h3.2.2.2.2 x hx, h5.2.2.2.2 x hx,
      h2.2.2.2.2 x hx, CState.ext_weval h1.1 x hx (a (Fin.last m)) (ha _),
      CState.ext_weval h02 x hx (b (Fin.last m)) (hb _),
      h4.2.2.2.2 x hx, CState.ext_weval h03 x hx (a (Fin.last m)) (ha _),
      CState.ext_weval h03 x hx (b (Fin.last m)) (hb _),
      CState.ext_weval h14 x hx lt_lo h1.2.2.1, h1.2.2.2.2 x hx]
    have ha_eq : bvVal s x a = bvVal s x (fun i => a i.castSucc) + 2 ^ m * (s.weval x (a (Fin.last m))).toNat := by
      unfold bvVal; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
      cases s.weval x (a (Fin.last m)) <;> simp
    have hb_eq : bvVal s x b = bvVal s x (fun i => b i.castSucc) + 2 ^ m * (s.weval x (b (Fin.last m))).toNat := by
      unfold bvVal; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
      cases s.weval x (b (Fin.last m)) <;> simp
    have hlo_a := bvVal_lt s x (fun i => a i.castSucc)
    have hlo_b := bvVal_lt s x (fun i => b i.castSucc)
    rw [ha_eq, hb_eq]
    cases s.weval x (a (Fin.last m)) <;> cases s.weval x (b (Fin.last m)) <;> simp <;> omega

def mkBvIte {n_in : ℕ} : (L : ℕ) → CState n_in → ℕ → BVec L → BVec L → CState n_in × BVec L
  | 0, s, _, _, _ => (s, Fin.elim0)
  | m + 1, s, c, a, b =>
    let (s1, vlo) := mkBvIte m s c (fun i => a i.castSucc) (fun i => b i.castSucc)
    let (s2, hi) := mkIte s1 c (a (Fin.last m)) (b (Fin.last m))
    (s2, Fin.snoc vlo hi)

lemma mkBvIte_spec {n_in : ℕ} (L : ℕ) (s : CState n_in) (hs : s.Valid) (c : ℕ) (a b : BVec L)
    (hc : c < s.nw) (ha : ∀ i, a i < s.nw) (hb : ∀ i, b i < s.nw) :
    let r := mkBvIte L s c a b
    s.Ext r.1 ∧ r.1.Valid ∧ (∀ i, r.2 i < r.1.nw) ∧ r.1.gates.length = s.gates.length + 4 * L ∧
    ∀ x : List Bool, x.length = n_in →
      bvVal r.1 x r.2 = if s.weval x c then bvVal s x a else bvVal s x b := by
  induction L generalizing s with
  | zero =>
    refine ⟨CState.ext_refl s, hs, fun i => Fin.elim0 i, by simp [mkBvIte], ?_⟩
    intro x _; simp [mkBvIte, bvVal]
  | succ m ih =>
    dsimp only [mkBvIte]
    have h1 := ih s hs (fun i => a i.castSucc) (fun i => b i.castSucc) hc (fun i => ha _) (fun i => hb _)
    set s1 := (mkBvIte m s c (fun i => a i.castSucc) (fun i => b i.castSucc)).1
    set vlo := (mkBvIte m s c (fun i => a i.castSucc) (fun i => b i.castSucc)).2
    have h2 := mkIte_spec s1 h1.2.1 c (a (Fin.last m)) (b (Fin.last m))
      (lt_of_lt_of_le hc (CState.ext_nw h1.1))
      (lt_of_lt_of_le (ha _) (CState.ext_nw h1.1))
      (lt_of_lt_of_le (hb _) (CState.ext_nw h1.1))
    set s2 := (mkIte s1 c (a (Fin.last m)) (b (Fin.last m))).1
    set hi := (mkIte s1 c (a (Fin.last m)) (b (Fin.last m))).2
    refine ⟨CState.ext_trans h1.1 h2.1, h2.2.1, ?_,
      by have := h1.2.2.2.1; have := h2.2.2.2.1; dsimp only [s1, s2] at *; omega, ?_⟩
    · intro i
      refine Fin.lastCases (by rw [Fin.snoc_last]; exact h2.2.2.1)
        (fun j => by rw [Fin.snoc_castSucc]; exact lt_of_lt_of_le (h1.2.2.1 j) (CState.ext_nw h2.1)) i
    · intro x hx
      have hlo_eq : bvVal s2 x (Fin.snoc vlo hi) = bvVal s1 x vlo + 2 ^ m * (s2.weval x hi).toNat := by
        unfold bvVal; rw [Fin.sum_univ_castSucc]; simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        rw [Finset.sum_congr rfl (fun i _ => by rw [CState.ext_weval h2.1 x hx (vlo i) (h1.2.2.1 i)])]
        cases s2.weval x hi <;> simp
      have ha_eq : bvVal s x a = bvVal s x (fun i => a i.castSucc) + 2 ^ m * (s.weval x (a (Fin.last m))).toNat := by
        unfold bvVal; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
        cases s.weval x (a (Fin.last m)) <;> simp
      have hb_eq : bvVal s x b = bvVal s x (fun i => b i.castSucc) + 2 ^ m * (s.weval x (b (Fin.last m))).toNat := by
        unfold bvVal; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
        cases s.weval x (b (Fin.last m)) <;> simp
      rw [hlo_eq, h1.2.2.2.2 x hx, h2.2.2.2.2 x hx,
        CState.ext_weval h1.1 x hx c hc,
        CState.ext_weval h1.1 x hx (a (Fin.last m)) (ha _),
        CState.ext_weval h1.1 x hx (b (Fin.last m)) (hb _),
        ha_eq, hb_eq]
      cases s.weval x c <;> simp

def mkBvShift {n_in L : ℕ} (s : CState n_in) (a : BVec L) (sh : ℕ) : CState n_in × BVec L :=
  let (s0, z) := mkConst s false
  (s0, fun i => if h : sh ≤ i.val then a ⟨i.val - sh, by omega⟩ else z)

lemma mkBvShift_spec {n_in L : ℕ} (s : CState n_in) (hs : s.Valid) (a : BVec L) (sh : ℕ)
    (ha : ∀ i, a i < s.nw) :
    let r := mkBvShift s a sh
    s.Ext r.1 ∧ r.1.Valid ∧ (∀ i, r.2 i < r.1.nw) ∧ r.1.gates.length = s.gates.length + 1 ∧
    ∀ x : List Bool, x.length = n_in → bvVal r.1 x r.2 = (bvVal s x a * 2 ^ sh) % 2 ^ L := by
  dsimp only [mkBvShift]
  have h0 := mkConst_spec s hs false
  set s0 := (mkConst s false).1; set z := (mkConst s false).2
  refine ⟨h0.1, h0.2.1, ?_, h0.2.2.2.1, ?_⟩
  · intro i; split_ifs
    · exact lt_of_lt_of_le (ha _) (CState.ext_nw h0.1)
    · exact h0.2.2.1
  · intro x hx
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < L
    · let jf : Fin L := ⟨j, hj⟩
      rw [bvVal_testBit s0 x _ jf, Nat.testBit_mod_two_pow]
      simp only [jf, hj, decide_true, Bool.true_and]
      rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
      split_ifs with hsh
      · rw [CState.ext_weval h0.1 x hx _ (ha _)]
        have htb := bvVal_testBit s x a ⟨j - sh, by omega⟩
        simp [hsh, htb]
      · simp [hsh]; exact h0.2.2.2.2 x hx
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (bvVal_lt s0 x _) (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_mod_two_pow]
      simp [hj]

def mkBvScaleAux {n_in L : ℕ} : ℕ → CState n_in → ℕ → BVec L → CState n_in × BVec L
  | 0, s, _, _ => mkBvConst s L 0
  | m + 1, s, c, a =>
    let (s1, acc) := mkBvScaleAux m s c a
    if c.testBit m then
      let (s2, sh) := mkBvShift s1 a m
      mkBvAdd s2 acc sh
    else
      (s1, acc)

lemma mkBvScaleAux_spec {n_in L : ℕ} (j : ℕ) (s : CState n_in) (hs : s.Valid) (c : ℕ) (a : BVec L)
    (ha : ∀ i, a i < s.nw) :
    let r := mkBvScaleAux j s c a
    s.Ext r.1 ∧ r.1.Valid ∧ (∀ i, r.2 i < r.1.nw) ∧
    r.1.gates.length ≤ s.gates.length + 2 + j * (13 * L + 2) ∧
    ∀ x : List Bool, x.length = n_in → bvVal r.1 x r.2 = ((c % 2 ^ j) * bvVal s x a) % 2 ^ L := by
  induction j generalizing s with
  | zero =>
    have h0 := mkBvConst_spec s hs L 0
    refine ⟨h0.1, h0.2.1, h0.2.2.1, by simp [mkBvScaleAux, h0.2.2.2.1], ?_⟩
    intro x hx; simp [mkBvScaleAux, h0.2.2.2.2 x hx, Nat.mod_one]
  | succ m ih =>
    dsimp only [mkBvScaleAux]
    have h1 := ih s hs ha
    set s1 := (mkBvScaleAux m s c a).1; set acc := (mkBvScaleAux m s c a).2
    have hmod_step : c % 2 ^ (m + 1) = c % 2 ^ m + if c.testBit m then 2 ^ m else 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < m
      · rw [Nat.testBit_mod_two_pow]
        have hi' : i < m + 1 := by omega
        simp only [hi', decide_true, Bool.true_and]
        cases hb : c.testBit m
        · simp [Nat.testBit_mod_two_pow, hi]
        · simp only [↓reduceIte]
          rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hi, Nat.testBit_mod_two_pow]
          simp [hi]
      · by_cases him : i = m
        · subst him
          rw [Nat.testBit_mod_two_pow]
          simp only [lt_add_iff_pos_right, zero_lt_one, decide_true, Bool.true_and]
          have hlt : c % 2 ^ i < 2 ^ i := Nat.mod_lt c (by positivity)
          cases hb : c.testBit i
          · simp [Nat.testBit_lt_two_pow hlt]
          · simp only [↓reduceIte]
            rw [Nat.add_comm (c % 2 ^ i), Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; rfl
        · have hgt : m + 1 ≤ i := by omega
          rw [Nat.testBit_mod_two_pow]
          have hnot : ¬ i < m + 1 := by omega
          simp only [hnot, decide_false, Bool.false_and]
          have hlt : c % 2 ^ m + (if c.testBit m = true then 2 ^ m else 0) < 2 ^ i := by
            have h1' : c % 2 ^ m < 2 ^ m := Nat.mod_lt c (by positivity)
            have h2' : 2 ^ (m + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hgt
            have h3' : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
            split_ifs <;> omega
          exact (Nat.testBit_lt_two_pow hlt).symm
    split_ifs with hbit
    · have h2 := mkBvShift_spec s1 h1.2.1 a m (fun i => lt_of_lt_of_le (ha i) (CState.ext_nw h1.1))
      set s2 := (mkBvShift s1 a m).1; set sh := (mkBvShift s1 a m).2
      have h3 := mkBvAdd_spec s2 h2.2.1 acc sh
        (fun i => lt_of_lt_of_le (h1.2.2.1 i) (CState.ext_nw h2.1)) h2.2.2.1
      refine ⟨CState.ext_trans h1.1 (CState.ext_trans h2.1 h3.1), h3.2.1, h3.2.2.1, ?_, ?_⟩
      · have := h1.2.2.2.1; have := h2.2.2.2.1; have := h3.2.2.2.1
        dsimp only [s1, s2] at *
        rw [Nat.add_mul, one_mul]; omega
      · intro x hx
        rw [h3.2.2.2.2 x hx, bvVal_ext h2.1 x hx acc h1.2.2.1, h1.2.2.2.2 x hx,
          h2.2.2.2.2 x hx, bvVal_ext h1.1 x hx a ha, hmod_step, hbit]
        simp only [↓reduceIte]
        rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_mul, Nat.mul_comm (2 ^ m)]
    · refine ⟨h1.1, h1.2.1, h1.2.2.1, ?_, ?_⟩
      · have := h1.2.2.2.1; dsimp only [s1] at *; rw [Nat.add_mul, one_mul]; omega
      · intro x hx
        rw [h1.2.2.2.2 x hx, hmod_step]
        simp [hbit]

def mkBvScale {n_in L : ℕ} (s : CState n_in) (c : ℕ) (a : BVec L) : CState n_in × BVec L :=
  mkBvScaleAux L s c a

lemma mkBvScale_spec {n_in L : ℕ} (s : CState n_in) (hs : s.Valid) (c : ℕ) (a : BVec L)
    (ha : ∀ i, a i < s.nw) :
    let r := mkBvScale s c a
    s.Ext r.1 ∧ r.1.Valid ∧ (∀ i, r.2 i < r.1.nw) ∧
    r.1.gates.length ≤ s.gates.length + 2 + L * (13 * L + 2) ∧
    ∀ x : List Bool, x.length = n_in → bvVal r.1 x r.2 = (c * bvVal s x a) % 2 ^ L := by
  have h := mkBvScaleAux_spec L s hs c a ha
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro x hx
  dsimp only [mkBvScale]
  rw [h.2.2.2.2 x hx, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

def mkBvEqConstAux {n_in : ℕ} : (L : ℕ) → CState n_in → BVec L → ℕ → CState n_in × ℕ
  | 0, s, _, _ => mkConst s true
  | m + 1, s, a, c =>
    let (s1, lo) := mkBvEqConstAux m s (fun i => a i.castSucc) c
    let (s2, bit) := if c.testBit m then (s1, a (Fin.last m)) else mkNot s1 (a (Fin.last m))
    mkAnd s2 lo bit

lemma mkBvEqConst_spec {n_in : ℕ} (L : ℕ) (s : CState n_in) (hs : s.Valid) (a : BVec L) (c : ℕ)
    (hc : c < 2 ^ L) (ha : ∀ i, a i < s.nw) :
    let r := mkBvEqConstAux L s a c
    s.Ext r.1 ∧ r.1.Valid ∧ r.2 < r.1.nw ∧ r.1.gates.length ≤ s.gates.length + 2 * L + 1 ∧
    ∀ x : List Bool, x.length = n_in → r.1.weval x r.2 = decide (bvVal s x a = c) := by
  induction L generalizing s c with
  | zero =>
    have hc0 : c = 0 := by simp at hc; omega
    subst hc0
    have h0 := mkConst_spec s hs true
    refine ⟨h0.1, h0.2.1, h0.2.2.1, by simp [mkBvEqConstAux, h0.2.2.2.1], ?_⟩
    intro x hx; simp [mkBvEqConstAux, h0.2.2.2.2 x hx, bvVal]
  | succ m ih =>
    dsimp only [mkBvEqConstAux]
    have h1 := ih s hs (fun i => a i.castSucc) (c % 2 ^ m) (Nat.mod_lt c (by positivity)) (fun i => ha _)

    have hcongr : ∀ m' (s' : CState n_in) (a' : BVec m') (c₁ c₂ : ℕ), (∀ i < m', c₁.testBit i = c₂.testBit i) →
        mkBvEqConstAux m' s' a' c₁ = mkBvEqConstAux m' s' a' c₂ := by
      intro m'
      induction m' with
      | zero => intros; rfl
      | succ k ihk =>
        intro s' a' c₁ c₂ htb
        simp only [mkBvEqConstAux, htb k (by omega)]
        rw [ihk s' (fun i => a' i.castSucc) c₁ c₂ (fun i hi => htb i (by omega))]
    have hcm : mkBvEqConstAux m s (fun i => a i.castSucc) c =
        mkBvEqConstAux m s (fun i => a i.castSucc) (c % 2 ^ m) :=
      hcongr m s _ c (c % 2 ^ m) (fun i hi => by simp [Nat.testBit_mod_two_pow, hi])
    rw [hcm]
    set s1 := (mkBvEqConstAux m s (fun i => a i.castSucc) (c % 2 ^ m)).1
    set lo := (mkBvEqConstAux m s (fun i => a i.castSucc) (c % 2 ^ m)).2
    have hbit_eq : c = c % 2 ^ m + 2 ^ m * (c.testBit m).toNat := by
      have hdiv := Nat.div_add_mod c (2 ^ m)
      have hq : c / 2 ^ m < 2 := by
        have : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
        rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
      have htb : c.testBit m = decide (c / 2 ^ m = 1) := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
        interval_cases (c / 2 ^ m) <;> rfl
      rw [htb]
      interval_cases (c / 2 ^ m) <;> simp at hdiv ⊢ <;> omega
    have ha_eq : ∀ x, bvVal s x a = bvVal s x (fun i => a i.castSucc) + 2 ^ m * (s.weval x (a (Fin.last m))).toNat := by
      intro x; unfold bvVal; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
      cases s.weval x (a (Fin.last m)) <;> simp
    split_ifs with hcb
    · have h2 := mkAnd_spec s1 h1.2.1 lo (a (Fin.last m)) h1.2.2.1
        (lt_of_lt_of_le (ha _) (CState.ext_nw h1.1))
      refine ⟨CState.ext_trans h1.1 h2.1, h2.2.1, h2.2.2.1,
        by have := h1.2.2.2.1; have := h2.2.2.2.1; dsimp only [s1] at *; omega, ?_⟩
      intro x hx
      rw [h2.2.2.2.2 x hx, h1.2.2.2.2 x hx, CState.ext_weval h1.1 x hx _ (ha _), ha_eq x]
      have hlo_a := bvVal_lt s x (fun i => a i.castSucc)
      have hlo_c : c % 2 ^ m < 2 ^ m := Nat.mod_lt c (by positivity)
      rw [hcb] at hbit_eq
      cases s.weval x (a (Fin.last m)) <;> simp at hbit_eq ⊢ <;> omega
    · have hn := mkNot_spec s1 h1.2.1 (a (Fin.last m)) (lt_of_lt_of_le (ha _) (CState.ext_nw h1.1))
      have h2 := mkAnd_spec _ hn.2.1 lo _ (lt_of_lt_of_le h1.2.2.1 (CState.ext_nw hn.1)) hn.2.2.1
      refine ⟨CState.ext_trans h1.1 (CState.ext_trans hn.1 h2.1), h2.2.1, h2.2.2.1,
        by have := h1.2.2.2.1; have := hn.2.2.2.1; have := h2.2.2.2.1; dsimp only [s1] at *; omega, ?_⟩
      intro x hx
      rw [h2.2.2.2.2 x hx, CState.ext_weval hn.1 x hx lo h1.2.2.1, h1.2.2.2.2 x hx,
        hn.2.2.2.2 x hx, CState.ext_weval h1.1 x hx _ (ha _), ha_eq x]
      have hlo_a := bvVal_lt s x (fun i => a i.castSucc)
      have hlo_c : c % 2 ^ m < 2 ^ m := Nat.mod_lt c (by positivity)
      have hcb_f : c.testBit m = false := Bool.eq_false_iff.mpr hcb
      rw [hcb_f] at hbit_eq
      cases s.weval x (a (Fin.last m)) <;> simp at hbit_eq ⊢ <;> omega

def tileOp (p n w : ℕ) : ℕ :=
  (List.range p).foldl (fun z a => z ||| (w <<< (a * n))) 0

def rotOp (k h w : ℕ) : ℕ :=
  ((w <<< (h % k)) ||| (w >>> (k - h % k))) % 2 ^ k

def stepOp (k w : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i => acc ||| ((xor (w.testBit i)
    (!(w.testBit ((i + 1) % k)) && w.testBit ((i + 2) % k))).toNat <<< i)) 0

def reachOp (r : ℕ) (col : Bool) : ℕ := if col then 7 * r - 2 else 5 * r - 3
def delayOp (r : ℕ) (col : Bool) : ℕ := if col then 3 * r + 1 else 2 * r - 2

def stateAux (p n r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2 ^ n)) : ℕ → ℕ
  | 0 => rotOp (p * n) (if col then 3 else 1) w ^^^ name
  | j + 1 =>
    let k := p * n
    let g := if col then 2 else 1
    let x := stateAux p n r col w name c j
    let cj := if h : j < r then (c ⟨j, h⟩).val else 0
    stepOp k (x ^^^ rotOp k g x ^^^ rotOp k (k - g) x) ^^^
      rotOp k (if col then 3 * (j + 1) + 1 else 2 * j) w ^^^ tileOp p n cj

lemma foldl_or_testBit {α : Type*} (l : List α) (f : α → ℕ) (z i : ℕ) :
    (l.foldl (fun acc a => acc ||| f a) z).testBit i =
      (z.testBit i || l.any (fun a => (f a).testBit i)) := by
  induction l generalizing z with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.any_cons, ih, Nat.testBit_or, Bool.or_assoc]

lemma foldl_or_lt_two_pow {α : Type*} (l : List α) (f : α → ℕ) (z B : ℕ)
    (hz : z < 2 ^ B) (hf : ∀ a ∈ l, f a < 2 ^ B) :
    l.foldl (fun acc a => acc ||| f a) z < 2 ^ B := by
  induction l generalizing z with
  | nil => exact hz
  | cons a t ih =>
    apply ih
    · exact Nat.or_lt_two_pow hz (hf a (by simp))
    · intro b hb; exact hf b (by simp [hb])

lemma tileOp_lt (p n w : ℕ) (hw : w < 2 ^ n) : tileOp p n w < 2 ^ (p * n) := by
  unfold tileOp
  apply foldl_or_lt_two_pow _ _ 0 (p * n) (by positivity)
  intro a ha
  rw [List.mem_range] at ha
  rw [Nat.shiftLeft_eq]
  have h1 : w * 2 ^ (a * n) < 2 ^ n * 2 ^ (a * n) := Nat.mul_lt_mul_of_pos_right hw (by positivity)
  have h2 : 2 ^ n * 2 ^ (a * n) = 2 ^ ((a + 1) * n) := by rw [← pow_add]; congr 1; ring
  have h3 : (a + 1) * n ≤ p * n := Nat.mul_le_mul_right n (by omega)
  exact lt_of_lt_of_le (by rw [← h2]; exact h1) (Nat.pow_le_pow_right (by omega) h3)

lemma tileOp_testBit (p n w i : ℕ) (hw : w < 2 ^ n) (hi : i < p * n) (hn : 0 < n) :
    (tileOp p n w).testBit i = w.testBit (i % n) := by
  unfold tileOp
  rw [foldl_or_testBit]
  simp only [Nat.zero_testBit, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, ha, htb⟩
    rw [List.mem_range] at ha
    rw [Nat.testBit_shiftLeft] at htb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htb
    have hlt : i - a * n < n := by
      by_contra hge
      have htb0 := Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hge)))
      rw [htb0] at htb; exact Bool.false_ne_true htb.2
    have hdiv : i / n = a := by
      have h1 : a * n ≤ i := htb.1
      have h2 : i < (a + 1) * n := by rw [Nat.add_mul, one_mul]; omega
      exact Nat.div_eq_of_lt_le h1 h2
    have hmod : i - a * n = i % n := by
      have := Nat.div_add_mod i n
      rw [hdiv, Nat.mul_comm] at this; omega
    rw [← hmod]; exact htb.2
  · intro htb
    refine ⟨i / n, List.mem_range.mpr ((Nat.div_lt_iff_lt_mul hn).mpr hi), ?_⟩
    rw [Nat.testBit_shiftLeft]
    have hle : i / n * n ≤ i := Nat.div_mul_le_self i n
    have hsub : i - i / n * n = i % n := by have := Nat.div_add_mod i n; rw [Nat.mul_comm] at this; omega
    simp [hle, hsub, htb]

lemma rotOp_lt (k h w : ℕ) : rotOp k h w < 2 ^ k :=
  Nat.mod_lt _ (by positivity)

lemma rotOp_testBit (k h w i : ℕ) (hk : 0 < k) (hw : w < 2 ^ k) (hi : i < k) :
    (rotOp k h w).testBit i = w.testBit ((i + k - h % k) % k) := by
  unfold rotOp
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hs : h % k < k := Nat.mod_lt h hk
  by_cases hge : h % k ≤ i
  · have hge2 : k ≤ k - h % k + i := by omega
    have hzero : w.testBit (k - h % k + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hge2))
    have hmod : (i + k - h % k) % k = i - h % k := by
      have : i + k - h % k = (i - h % k) + k := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp [hge, hzero, hmod]
  · have hlt : i < h % k := by omega
    have hmod : (i + k - h % k) % k = k - h % k + i := by
      have : i + k - h % k = k - h % k + i := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    simp [hge, hmod]

lemma stepOp_lt (k w : ℕ) : stepOp k w < 2 ^ k := by
  unfold stepOp
  apply foldl_or_lt_two_pow _ _ 0 k (by positivity)
  intro i hi
  rw [List.mem_range] at hi
  rw [Nat.shiftLeft_eq]
  have h1 : (xor (w.testBit i) (!(w.testBit ((i + 1) % k)) && w.testBit ((i + 2) % k))).toNat ≤ 1 := by
    cases xor (w.testBit i) (!(w.testBit ((i + 1) % k)) && w.testBit ((i + 2) % k)) <;> decide
  have h2 : 1 * 2 ^ i < 2 ^ k := by rw [one_mul]; exact Nat.pow_lt_pow_right (by omega) hi
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ h1) h2

lemma stepOp_testBit (k w i : ℕ) (hi : i < k) :
    (stepOp k w).testBit i =
      xor (w.testBit i) (!(w.testBit ((i + 1) % k)) && w.testBit ((i + 2) % k)) := by
  unfold stepOp
  rw [foldl_or_testBit]
  simp only [Nat.zero_testBit, Bool.false_or]
  set f : ℕ → Bool := fun j => xor (w.testBit j) (!(w.testBit ((j + 1) % k)) && w.testBit ((j + 2) % k))
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, htb⟩
    rw [Nat.testBit_shiftLeft] at htb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htb
    have hij : i - j = 0 := by
      by_contra hne
      have hge1 : 1 ≤ i - j := by omega
      have hlt2 : (f j).toNat < 2 ^ (i - j) := by
        have : (f j).toNat < 2 ^ 1 := by cases f j <;> decide
        exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) hge1)
      rw [Nat.testBit_lt_two_pow hlt2] at htb; exact Bool.false_ne_true htb.2
    have hjeq : j = i := by omega
    subst hjeq
    rw [hij] at htb
    cases hfj : f j <;> dsimp only [f] at hfj <;> rw [hfj] at htb ⊢ <;> simp at htb ⊢
  · intro hfi
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    rw [Nat.testBit_shiftLeft]
    simp [hfi]

lemma stateAux_lt (p n r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2 ^ n))
    (hname : name < 2 ^ (p * n)) (t : ℕ) :
    stateAux p n r col w name c t < 2 ^ (p * n) := by
  induction t with
  | zero =>
    exact Nat.xor_lt_two_pow (rotOp_lt _ _ _) hname
  | succ j _ =>
    dsimp only [stateAux]
    refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepOp_lt _ _) (rotOp_lt _ _ _)) ?_
    split_ifs with h
    · exact tileOp_lt p n _ (c ⟨j, h⟩).isLt
    · exact tileOp_lt p n 0 (by positivity)

lemma stateAux_eq_foldl (p n r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2 ^ n)) :
    stateAux p n r col w name c r =
      (List.finRange r).foldl (fun x j =>
        let k := p * n
        let g := if col then 2 else 1
        stepOp k (x ^^^ rotOp k g x ^^^ rotOp k (k - g) x) ^^^
          rotOp k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ tileOp p n (c j).val)
        (rotOp (p * n) (if col then 3 else 1) w ^^^ name) := by
  have hgen : ∀ m (hm : m ≤ r),
      stateAux p n r col w name c m =
        ((List.finRange r).take m).foldl (fun x j =>
          let k := p * n
          let g := if col then 2 else 1
          stepOp k (x ^^^ rotOp k g x ^^^ rotOp k (k - g) x) ^^^
            rotOp k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ tileOp p n (c j).val)
          (rotOp (p * n) (if col then 3 else 1) w ^^^ name) := by
    intro m hm
    induction m with
    | zero => simp [stateAux]
    | succ j ih =>
      have htake : (List.finRange r).take (j + 1) = (List.finRange r).take j ++ [⟨j, hm⟩] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega)]
        simp [List.getElem_finRange]
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih (by omega)]
      have hjr : j < r := hm
      simp [stateAux, hjr]
  have h := hgen r le_rfl
  rw [List.take_of_length_le (by simp)] at h
  exact h

def locState (n r : ℕ) (col : Bool) (wWin : ℕ → Bool) (nameBit : ℕ → Bool)
    (cBit : Fin r → ℕ → Bool) (i0 : ℕ) : ℕ → ℕ → Bool
  | 0, q => xor (wWin (q - if col then 3 else 1)) (nameBit ((i0 + q) % n))
  | j + 1, q =>
    let g := if col then 2 else 1
    let x := locState n r col wWin nameBit cBit i0 j
    let lin := fun u => xor (xor (x u) (x (u - g))) (x (u + g))
    let st := xor (lin q) (!(lin (q + 1)) && lin (q + 2))
    let hw := if col then 3 * (j + 1) + 1 else 2 * j
    let cb := if h : j < r then cBit ⟨j, h⟩ ((i0 + q) % n) else false
    xor (xor st (wWin (q - hw))) cb

lemma locState_eq_stateAux (p n r d : ℕ) (hp : 2 ≤ p) (hd : 0 < d) (hdn : d < n) (hr : 4 ≤ r)
    (col : Bool) (hreach : reachOp r col ≤ d)
    (w : Fin (2 ^ (p * n))) (name : Fin (2 ^ n)) (c : Fin r → Fin (2 ^ n))
    (i : Fin n) (a : Fin p) :
    let k := p * n
    let p0 := a.val * n + i.val
    let wWin := fun idx => w.val.testBit ((p0 + idx) % k)
    (stateAux p n r col w.val (tileOp p n name.val) c r).testBit ((p0 + delayOp r col) % k) =
      locState n r col wWin (fun u => name.val.testBit u) (fun j u => (c j).val.testBit u) i.val r (delayOp r col) := by
  intro k p0 wWin
  have hn : 0 < n := by omega
  have hk : 0 < k := Nat.mul_pos (by omega) hn
  have hk4 : 4 ≤ k := by have : 2 * 2 ≤ p * n := Nat.mul_le_mul hp (by omega); omega
  let g := if col then 2 else 1
  have hg_lt : g < k := by dsimp [g]; cases col <;> simp <;> omega
  have hdk : d < k := lt_of_lt_of_le hdn (Nat.le_mul_of_pos_left n (by omega))

  have hmain : ∀ t (ht : t ≤ r) (q : ℕ),
      delayOp r col - (r - t) * g ≤ q →
      q ≤ delayOp r col + (r - t) * (g + 2) →
      (stateAux p n r col w.val (tileOp p n name.val) c t).testBit ((p0 + q) % k) =
        locState n r col wWin (fun u => name.val.testBit u) (fun j u => (c j).val.testBit u) i.val t q := by
    intro t
    induction t with
    | zero =>
      intro _ q hlo hhi
      dsimp only [stateAux, locState]
      rw [Nat.testBit_xor,
        rotOp_testBit k _ w.val _ hk w.isLt (Nat.mod_lt _ hk),
        tileOp_testBit p n name.val _ name.isLt (Nat.mod_lt _ hk) hn]
      have hinit_lt : (if col then 3 else 1) < k := by cases col <;> simp <;> omega
      have hinit_le : (if col then 3 else 1) ≤ q := by
        dsimp only [delayOp, reachOp, g] at hlo hreach ⊢
        cases col <;> simp at hlo hreach ⊢ <;> omega
      have hmod1 : ((p0 + q) % k + k - (if col then 3 else 1) % k) % k = (p0 + (q - if col then 3 else 1)) % k := by
        rw [Nat.mod_eq_of_lt hinit_lt]
        have h1 : (p0 + q) % k + k - (if col then 3 else 1) = (p0 + q) % k + (k - (if col then 3 else 1)) := by omega
        rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have h2 : p0 + q + (k - (if col then 3 else 1)) = p0 + (q - (if col then 3 else 1)) + k := by omega
        rw [h2, Nat.add_mod_right]
      have hmod2 : (p0 + q) % k % n = (i.val + q) % n := by
        have hkn : n ∣ k := ⟨p, by dsimp [k]; ring⟩
        rw [Nat.mod_mod_of_dvd _ hkn]
        have : p0 + q = (i.val + q) + a.val * n := by dsimp [p0]; ring
        rw [this, Nat.add_mul_mod_self_right]
      rw [hmod1, hmod2]
    | succ j ih =>
      intro hjr q hlo hhi
      have hlt_x : stateAux p n r col w.val (tileOp p n name.val) c j < 2 ^ k :=
        stateAux_lt p n r col w.val (tileOp p n name.val) c (tileOp_lt p n name.val name.isLt) j
      dsimp only [stateAux, locState]
      rw [Nat.testBit_xor, Nat.testBit_xor,
        stepOp_testBit k _ _ (Nat.mod_lt _ hk),
        rotOp_testBit k _ w.val _ hk w.isLt (Nat.mod_lt _ hk)]
      have hmod_n : (p0 + q) % k % n = (i.val + q) % n := by
        have hkn : n ∣ k := ⟨p, by dsimp [k]; ring⟩
        rw [Nat.mod_mod_of_dvd _ hkn]
        have : p0 + q = (i.val + q) + a.val * n := by dsimp [p0]; ring
        rw [this, Nat.add_mul_mod_self_right]
      have hc_eq : (tileOp p n (if h : j < r then (c ⟨j, h⟩).val else 0)).testBit ((p0 + q) % k) =
          if h : j < r then (c ⟨j, h⟩).val.testBit ((i.val + q) % n) else false := by
        split_ifs with h
        · rw [tileOp_testBit p n _ _ (c ⟨j, h⟩).isLt (Nat.mod_lt _ hk) hn, hmod_n]
        · omega
      have hhw_lt : (if col then 3 * (j + 1) + 1 else 2 * j) < k := by
        dsimp only [reachOp] at hreach
        cases col <;> simp at hreach ⊢ <;> omega
      have hhw_le : (if col then 3 * (j + 1) + 1 else 2 * j) ≤ q := by
        dsimp only [delayOp, g] at hlo ⊢
        cases col <;> simp at hlo ⊢ <;> omega
      have hmod_w : ((p0 + q) % k + k - (if col then 3 * (j + 1) + 1 else 2 * j) % k) % k =
          (p0 + (q - if col then 3 * (j + 1) + 1 else 2 * j)) % k := by
        rw [Nat.mod_eq_of_lt hhw_lt]
        have h1 : (p0 + q) % k + k - (if col then 3 * (j + 1) + 1 else 2 * j) =
            (p0 + q) % k + (k - (if col then 3 * (j + 1) + 1 else 2 * j)) := by omega
        rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have h2 : p0 + q + (k - (if col then 3 * (j + 1) + 1 else 2 * j)) =
            p0 + (q - if col then 3 * (j + 1) + 1 else 2 * j) + k := by omega
        rw [h2, Nat.add_mod_right]

      have hlin : ∀ δ ≤ 2,
          let x := stateAux p n r col w.val (tileOp p n name.val) c j
          let xl := locState n r col wWin (fun u => name.val.testBit u) (fun j u => (c j).val.testBit u) i.val j
          (x ^^^ rotOp k g x ^^^ rotOp k (k - g) x).testBit (((p0 + q) % k + δ) % k) =
            xor (xor (xl (q + δ)) (xl (q + δ - g))) (xl (q + δ + g)) := by
        intro δ hδ x xl
        have hpos : ((p0 + q) % k + δ) % k = (p0 + (q + δ)) % k := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
        rw [hpos, Nat.testBit_xor, Nat.testBit_xor,
          rotOp_testBit k g x _ hk hlt_x (Nat.mod_lt _ hk),
          rotOp_testBit k (k - g) x _ hk hlt_x (Nat.mod_lt _ hk)]
        have hq_ge_g : g ≤ q + δ := by
          dsimp only [delayOp, g] at hlo ⊢; cases col <;> simp at hlo ⊢ <;> omega
        have hmod_sub : ((p0 + (q + δ)) % k + k - g % k) % k = (p0 + (q + δ - g)) % k := by
          rw [Nat.mod_eq_of_lt hg_lt]
          have h1 : (p0 + (q + δ)) % k + k - g = (p0 + (q + δ)) % k + (k - g) := by omega
          rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have h2 : p0 + (q + δ) + (k - g) = p0 + (q + δ - g) + k := by omega
          rw [h2, Nat.add_mod_right]
        have hmod_add : ((p0 + (q + δ)) % k + k - (k - g) % k) % k = (p0 + (q + δ + g)) % k := by
          rw [Nat.mod_eq_of_lt (by have := hg_lt; dsimp [g] at *; cases col <;> simp at * <;> omega : k - g < k)]
          have h1 : (p0 + (q + δ)) % k + k - (k - g) = (p0 + (q + δ)) % k + g := by omega
          rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
        rw [hmod_sub, hmod_add]
        have hlo1 : delayOp r col - (r - j) * g ≤ q + δ := by
          have : (r - (j + 1)) * g + g = (r - j) * g := by
            have : r - j = r - (j + 1) + 1 := by omega
            rw [this, Nat.add_mul, one_mul]
          omega
        have hlo2 : delayOp r col - (r - j) * g ≤ q + δ - g := by
          have : (r - (j + 1)) * g + g = (r - j) * g := by
            have : r - j = r - (j + 1) + 1 := by omega
            rw [this, Nat.add_mul, one_mul]
          omega
        have hlo3 : delayOp r col - (r - j) * g ≤ q + δ + g := by omega
        have hhi_step : (r - (j + 1)) * (g + 2) + (g + 2) = (r - j) * (g + 2) := by
          have : r - j = r - (j + 1) + 1 := by omega
          rw [this, Nat.add_mul, one_mul]
        have hhi1 : q + δ ≤ delayOp r col + (r - j) * (g + 2) := by omega
        have hhi2 : q + δ - g ≤ delayOp r col + (r - j) * (g + 2) := by omega
        have hhi3 : q + δ + g ≤ delayOp r col + (r - j) * (g + 2) := by omega
        rw [ih (by omega) (q + δ) hlo1 hhi1,
            ih (by omega) (q + δ - g) hlo2 hhi2,
            ih (by omega) (q + δ + g) hlo3 hhi3]
      have h0 := hlin 0 (by omega); simp only [add_zero, Nat.mod_mod] at h0
      have h1 := hlin 1 (by omega)
      have h2 := hlin 2 (by omega)
      rw [h0, h1, h2, hmod_w, hc_eq]
  exact hmain r le_rfl (delayOp r col) (by simp) (by simp)

lemma locState_congr (n r d : ℕ) (hr : 4 ≤ r) (col : Bool) (hreach : reachOp r col ≤ d)
    (wWin₁ wWin₂ : ℕ → Bool) (hw : ∀ idx ≤ d, wWin₁ idx = wWin₂ idx)
    (nameBit : ℕ → Bool) (cBit : Fin r → ℕ → Bool) (i0 : ℕ) :
    locState n r col wWin₁ nameBit cBit i0 r (delayOp r col) =
      locState n r col wWin₂ nameBit cBit i0 r (delayOp r col) := by
  let g := if col then 2 else 1
  have hmain : ∀ t (ht : t ≤ r) (q : ℕ),
      delayOp r col - (r - t) * g ≤ q →
      q ≤ delayOp r col + (r - t) * (g + 2) →
      locState n r col wWin₁ nameBit cBit i0 t q = locState n r col wWin₂ nameBit cBit i0 t q := by
    intro t
    induction t with
    | zero =>
      intro _ q _ hhi
      dsimp only [locState]
      have hidx : q - (if col then 3 else 1) ≤ d := by
        dsimp only [delayOp, reachOp, g] at hhi hreach ⊢
        cases col <;> simp at hhi hreach ⊢ <;> omega
      rw [hw _ hidx]
    | succ j ih =>
      intro hjr q hlo hhi
      dsimp only [locState]
      have hidx : q - (if col then 3 * (j + 1) + 1 else 2 * j) ≤ d := by
        dsimp only [delayOp, reachOp, g] at hhi hreach ⊢
        cases col <;> simp at hhi hreach ⊢ <;> omega
      have hsub : ∀ δ ≤ 2,
          locState n r col wWin₁ nameBit cBit i0 j (q + δ) = locState n r col wWin₂ nameBit cBit i0 j (q + δ) ∧
          locState n r col wWin₁ nameBit cBit i0 j (q + δ - g) = locState n r col wWin₂ nameBit cBit i0 j (q + δ - g) ∧
          locState n r col wWin₁ nameBit cBit i0 j (q + δ + g) = locState n r col wWin₂ nameBit cBit i0 j (q + δ + g) := by
        intro δ hδ
        have hstep1 : (r - (j + 1)) * g + g = (r - j) * g := by
          have : r - j = r - (j + 1) + 1 := by omega
          rw [this, Nat.add_mul, one_mul]
        have hstep2 : (r - (j + 1)) * (g + 2) + (g + 2) = (r - j) * (g + 2) := by
          have : r - j = r - (j + 1) + 1 := by omega
          rw [this, Nat.add_mul, one_mul]
        exact ⟨ih (by omega) (q + δ) (by omega) (by omega),
          ih (by omega) (q + δ - g) (by omega) (by omega),
          ih (by omega) (q + δ + g) (by omega) (by omega)⟩
      have h0 := hsub 0 (by omega); simp only [add_zero] at h0
      have h1 := hsub 1 (by omega)
      have h2 := hsub 2 (by omega)
      rw [h0.1, h0.2.1, h0.2.2, h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1, h2.2.2, hw _ hidx]
  exact hmain r le_rfl (delayOp r col) (by simp) (by simp)

def locSensor (n r d : ℕ) (col : Bool) (nameBit : ℕ → Bool) (cBit : Fin r → ℕ → Bool)
    (i0 : ℕ) (v : Fin (2 ^ d)) (b : Bool) : Bool :=
  locState n r col (fun idx => if idx < d then v.val.testBit idx else b) nameBit cBit i0 r (delayOp r col)

def mkLocLayer0 {n_in : ℕ} (n : ℕ) (col : Bool) (wWin : ℕ → Bool) (nameW : ℕ → ℕ) (i0 : ℕ) :
    (Q : ℕ) → CState n_in → CState n_in × (Fin Q → ℕ)
  | 0, s => (s, Fin.elim0)
  | m + 1, s =>
    let (s1, lo) := mkLocLayer0 n col wWin nameW i0 m s
    let (s2, wc) := mkConst s1 (wWin (m - if col then 3 else 1))
    let (s3, bit) := mkXor s2 wc (nameW ((i0 + m) % n))
    (s3, Fin.snoc lo bit)

lemma mkLocLayer0_spec {n_in : ℕ} (n : ℕ) (col : Bool) (wWin : ℕ → Bool) (nameW : ℕ → ℕ) (i0 : ℕ)
    (Q : ℕ) (s : CState n_in) (hs : s.Valid) (hname : ∀ u, nameW u < s.nw) :
    let r := mkLocLayer0 n col wWin nameW i0 Q s
    s.Ext r.1 ∧ r.1.Valid ∧ (∀ q : Fin Q, r.2 q < r.1.nw) ∧
    r.1.gates.length = s.gates.length + 6 * Q ∧
    ∀ x : List Bool, x.length = n_in → ∀ q : Fin Q,
      r.1.weval x (r.2 q) = xor (wWin (q.val - if col then 3 else 1)) (s.weval x (nameW ((i0 + q.val) % n))) := by
  induction Q generalizing s with
  | zero =>
    refine ⟨CState.ext_refl s, hs, fun q => Fin.elim0 q, by simp [mkLocLayer0], ?_⟩
    intro x _ q; exact Fin.elim0 q
  | succ m ih =>
    dsimp only [mkLocLayer0]
    have h1 := ih s hs hname
    set s1 := (mkLocLayer0 n col wWin nameW i0 m s).1
    set lo := (mkLocLayer0 n col wWin nameW i0 m s).2
    have h2 := mkConst_spec s1 h1.2.1 (wWin (m - if col then 3 else 1))
    set s2 := (mkConst s1 (wWin (m - if col then 3 else 1))).1
    set wc := (mkConst s1 (wWin (m - if col then 3 else 1))).2
    have h02 : s.Ext s2 := CState.ext_trans h1.1 h2.1
    have h3 := mkXor_spec s2 h2.2.1 wc (nameW ((i0 + m) % n)) h2.2.2.1
      (lt_of_lt_of_le (hname _) (CState.ext_nw h02))
    set s3 := (mkXor s2 wc (nameW ((i0 + m) % n))).1
    set bit := (mkXor s2 wc (nameW ((i0 + m) % n))).2
    have h13 : s1.Ext s3 := CState.ext_trans h2.1 h3.1
    refine ⟨CState.ext_trans h1.1 h13, h3.2.1, ?_,
      by have := h1.2.2.2.1; have := h2.2.2.2.1; have := h3.2.2.2.1; dsimp only [s1, s2, s3] at *; omega, ?_⟩
    · intro q
      refine Fin.lastCases (by rw [Fin.snoc_last]; exact h3.2.2.1)
        (fun j => by rw [Fin.snoc_castSucc]; exact lt_of_lt_of_le (h1.2.2.1 j) (CState.ext_nw h13)) q
    · intro x hx q
      refine Fin.lastCases ?_ ?_ q
      · rw [Fin.snoc_last, Fin.val_last, h3.2.2.2.2 x hx, h2.2.2.2.2 x hx,
          CState.ext_weval h02 x hx _ (hname _)]
      · intro j
        rw [Fin.snoc_castSucc, Fin.val_castSucc, CState.ext_weval h13 x hx (lo j) (h1.2.2.1 j)]
        exact h1.2.2.2.2 x hx j

def mkLocStep {n_in : ℕ} (n : ℕ) (col : Bool) (wWin : ℕ → Bool) (cW : ℕ → ℕ) (i0 j : ℕ)
    (Qprev : ℕ) (prev : Fin Qprev → ℕ) :
    (Q : ℕ) → CState n_in → CState n_in × (Fin Q → ℕ)
  | 0, s => (s, Fin.elim0)
  | m + 1, s =>
    let g := if col then 2 else 1
    let (s1, lo) := mkLocStep n col wWin cW i0 j Qprev prev m s
    let getPrev := fun u => if h : u < Qprev then prev ⟨u, h⟩ else 0

    let (s2, l0a) := mkXor s1 (getPrev m) (getPrev (m - g))
    let (s3, l0) := mkXor s2 l0a (getPrev (m + g))
    let (s4, l1a) := mkXor s3 (getPrev (m + 1)) (getPrev (m + 1 - g))
    let (s5, l1) := mkXor s4 l1a (getPrev (m + 1 + g))
    let (s6, l2a) := mkXor s5 (getPrev (m + 2)) (getPrev (m + 2 - g))
    let (s7, l2) := mkXor s6 l2a (getPrev (m + 2 + g))
    let (s8, nl1) := mkNot s7 l1
    let (s9, chi) := mkAnd s8 nl1 l2
    let (s10, st) := mkXor s9 l0 chi
    let (s11, wc) := mkConst s10 (wWin (m - if col then 3 * (j + 1) + 1 else 2 * j))
    let (s12, sw) := mkXor s11 st wc
    let (s13, bit) := mkXor s12 sw (cW ((i0 + m) % n))
    (s13, Fin.snoc lo bit)

lemma mkLocStep_spec {n_in : ℕ} (n : ℕ) (col : Bool) (wWin : ℕ → Bool) (cW : ℕ → ℕ) (i0 j : ℕ)
    (Qprev Q : ℕ) (hQ : Q + 4 ≤ Qprev) (prev : Fin Qprev → ℕ)
    (s : CState n_in) (hs : s.Valid) (hprev : ∀ u, prev u < s.nw) (hcW : ∀ u, cW u < s.nw) :
    let r := mkLocStep n col wWin cW i0 j Qprev prev Q s
    s.Ext r.1 ∧ r.1.Valid ∧ (∀ q : Fin Q, r.2 q < r.1.nw) ∧
    r.1.gates.length = s.gates.length + 48 * Q ∧
    ∀ x : List Bool, x.length = n_in → ∀ q : Fin Q,
      let g := if col then 2 else 1
      let xv := fun u => if h : u < Qprev then s.weval x (prev ⟨u, h⟩) else false
      let lin := fun u => xor (xor (xv u) (xv (u - g))) (xv (u + g))
      let st := xor (lin q.val) (!(lin (q.val + 1)) && lin (q.val + 2))
      r.1.weval x (r.2 q) =
        xor (xor st (wWin (q.val - if col then 3 * (j + 1) + 1 else 2 * j))) (s.weval x (cW ((i0 + q.val) % n))) := by
  induction Q generalizing s with
  | zero =>
    refine ⟨CState.ext_refl s, hs, fun q => Fin.elim0 q, by simp [mkLocStep], ?_⟩
    intro x _ q; exact Fin.elim0 q
  | succ m ih =>
    dsimp only [mkLocStep]
    let g := if col then 2 else 1
    have hgp : ∀ u ≤ m + 4, u < Qprev := fun u hu => by omega
    have hgp_lt : ∀ u ≤ m + 4, (if h : u < Qprev then prev ⟨u, h⟩ else 0) < s.nw := by
      intro u hu; rw [dif_pos (hgp u hu)]; exact hprev _
    have h1 := ih (by omega) s hs hprev hcW
    set s1 := (mkLocStep n col wWin cW i0 j Qprev prev m s).1
    set lo := (mkLocStep n col wWin cW i0 j Qprev prev m s).2
    let gp := fun u => if h : u < Qprev then prev ⟨u, h⟩ else 0
    have hgp_s1 : ∀ u ≤ m + 4, gp u < s1.nw := fun u hu => lt_of_lt_of_le (hgp_lt u hu) (CState.ext_nw h1.1)
    have h2 := mkXor_spec s1 h1.2.1 (gp m) (gp (m - g)) (hgp_s1 m (by omega)) (hgp_s1 (m - g) (by omega))
    set s2 := (mkXor s1 (gp m) (gp (m - g))).1; set l0a := (mkXor s1 (gp m) (gp (m - g))).2
    have h3 := mkXor_spec s2 h2.2.1 l0a (gp (m + g)) h2.2.2.1
      (lt_of_lt_of_le (hgp_s1 (m + g) (by dsimp [g]; cases col <;> simp <;> omega)) (CState.ext_nw h2.1))
    set s3 := (mkXor s2 l0a (gp (m + g))).1; set l0 := (mkXor s2 l0a (gp (m + g))).2
    have h13 : s1.Ext s3 := CState.ext_trans h2.1 h3.1
    have h4 := mkXor_spec s3 h3.2.1 (gp (m + 1)) (gp (m + 1 - g))
      (lt_of_lt_of_le (hgp_s1 (m + 1) (by omega)) (CState.ext_nw h13))
      (lt_of_lt_of_le (hgp_s1 (m + 1 - g) (by omega)) (CState.ext_nw h13))
    set s4 := (mkXor s3 (gp (m + 1)) (gp (m + 1 - g))).1; set l1a := (mkXor s3 (gp (m + 1)) (gp (m + 1 - g))).2
    have h14 : s1.Ext s4 := CState.ext_trans h13 h4.1
    have h5 := mkXor_spec s4 h4.2.1 l1a (gp (m + 1 + g)) h4.2.2.1
      (lt_of_lt_of_le (hgp_s1 (m + 1 + g) (by dsimp [g]; cases col <;> simp <;> omega)) (CState.ext_nw h14))
    set s5 := (mkXor s4 l1a (gp (m + 1 + g))).1; set l1 := (mkXor s4 l1a (gp (m + 1 + g))).2
    have h15 : s1.Ext s5 := CState.ext_trans h14 h5.1
    have h6 := mkXor_spec s5 h5.2.1 (gp (m + 2)) (gp (m + 2 - g))
      (lt_of_lt_of_le (hgp_s1 (m + 2) (by omega)) (CState.ext_nw h15))
      (lt_of_lt_of_le (hgp_s1 (m + 2 - g) (by omega)) (CState.ext_nw h15))
    set s6 := (mkXor s5 (gp (m + 2)) (gp (m + 2 - g))).1; set l2a := (mkXor s5 (gp (m + 2)) (gp (m + 2 - g))).2
    have h16 : s1.Ext s6 := CState.ext_trans h15 h6.1
    have h7 := mkXor_spec s6 h6.2.1 l2a (gp (m + 2 + g)) h6.2.2.1
      (lt_of_lt_of_le (hgp_s1 (m + 2 + g) (by dsimp [g]; cases col <;> simp <;> omega)) (CState.ext_nw h16))
    set s7 := (mkXor s6 l2a (gp (m + 2 + g))).1; set l2 := (mkXor s6 l2a (gp (m + 2 + g))).2
    have h57 : s5.Ext s7 := CState.ext_trans h6.1 h7.1
    have h8 := mkNot_spec s7 h7.2.1 l1 (lt_of_lt_of_le h5.2.2.1 (CState.ext_nw h57))
    set s8 := (mkNot s7 l1).1; set nl1 := (mkNot s7 l1).2
    have h9 := mkAnd_spec s8 h8.2.1 nl1 l2 h8.2.2.1 (lt_of_lt_of_le h7.2.2.1 (CState.ext_nw h8.1))
    set s9 := (mkAnd s8 nl1 l2).1; set chi := (mkAnd s8 nl1 l2).2
    have h39 : s3.Ext s9 := CState.ext_trans (CState.ext_trans h4.1 h5.1) (CState.ext_trans h57 (CState.ext_trans h8.1 h9.1))
    have h10 := mkXor_spec s9 h9.2.1 l0 chi (lt_of_lt_of_le h3.2.2.1 (CState.ext_nw h39)) h9.2.2.1
    set s10 := (mkXor s9 l0 chi).1; set st := (mkXor s9 l0 chi).2
    have h11 := mkConst_spec s10 h10.2.1 (wWin (m - if col then 3 * (j + 1) + 1 else 2 * j))
    set s11 := (mkConst s10 (wWin (m - if col then 3 * (j + 1) + 1 else 2 * j))).1
    set wc := (mkConst s10 (wWin (m - if col then 3 * (j + 1) + 1 else 2 * j))).2
    have h12 := mkXor_spec s11 h11.2.1 st wc (lt_of_lt_of_le h10.2.2.1 (CState.ext_nw h11.1)) h11.2.2.1
    set s12 := (mkXor s11 st wc).1; set sw := (mkXor s11 st wc).2
    have h1_12 : s1.Ext s12 := CState.ext_trans h13 (CState.ext_trans h39 (CState.ext_trans h10.1 (CState.ext_trans h11.1 h12.1)))
    have h0_12 : s.Ext s12 := CState.ext_trans h1.1 h1_12
    have h13' := mkXor_spec s12 h12.2.1 sw (cW ((i0 + m) % n)) h12.2.2.1
      (lt_of_lt_of_le (hcW _) (CState.ext_nw h0_12))
    set s13 := (mkXor s12 sw (cW ((i0 + m) % n))).1; set bit := (mkXor s12 sw (cW ((i0 + m) % n))).2
    have h1_13 : s1.Ext s13 := CState.ext_trans h1_12 h13'.1
    refine ⟨CState.ext_trans h1.1 h1_13, h13'.2.1, ?_, ?_, ?_⟩
    · intro q
      refine Fin.lastCases (by rw [Fin.snoc_last]; exact h13'.2.2.1)
        (fun k' => by rw [Fin.snoc_castSucc]; exact lt_of_lt_of_le (h1.2.2.1 k') (CState.ext_nw h1_13)) q
    · have := h1.2.2.2.1; have := h2.2.2.2.1; have := h3.2.2.2.1; have := h4.2.2.2.1
      have := h5.2.2.2.1; have := h6.2.2.2.1; have := h7.2.2.2.1; have := h8.2.2.2.1
      have := h9.2.2.2.1; have := h10.2.2.2.1; have := h11.2.2.2.1; have := h12.2.2.2.1; have := h13'.2.2.2.1
      dsimp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13] at *; omega
    · intro x hx q
      refine Fin.lastCases ?_ ?_ q
      · rw [Fin.snoc_last, Fin.val_last]
        have hgp_ev : ∀ u ≤ m + 4, s.weval x (gp u) = if h : u < Qprev then s.weval x (prev ⟨u, h⟩) else false := by
          intro u hu; dsimp only [gp]; rw [dif_pos (hgp u hu), dif_pos (hgp u hu)]
        rw [h13'.2.2.2.2 x hx, h12.2.2.2.2 x hx, CState.ext_weval h11.1 x hx st h10.2.2.1,
          h11.2.2.2.2 x hx, CState.ext_weval h0_12 x hx _ (hcW _),
          h10.2.2.2.2 x hx, CState.ext_weval h39 x hx l0 h3.2.2.1,
          h9.2.2.2.2 x hx, h8.2.2.2.2 x hx, CState.ext_weval h57 x hx l1 h5.2.2.1,
          CState.ext_weval h8.1 x hx l2 h7.2.2.1,
          h3.2.2.2.2 x hx, h2.2.2.2.2 x hx,
          h5.2.2.2.2 x hx, h4.2.2.2.2 x hx,
          h7.2.2.2.2 x hx, h6.2.2.2.2 x hx,
          CState.ext_weval (CState.ext_trans h1.1 h2.1) x hx _ (hgp_lt (m + g) (by dsimp [g]; cases col <;> simp <;> omega)),
          CState.ext_weval h1.1 x hx _ (hgp_lt m (by omega)),
          CState.ext_weval h1.1 x hx _ (hgp_lt (m - g) (by omega)),
          CState.ext_weval (CState.ext_trans h1.1 h13) x hx _ (hgp_lt (m + 1) (by omega)),
          CState.ext_weval (CState.ext_trans h1.1 h13) x hx _ (hgp_lt (m + 1 - g) (by omega)),
          CState.ext_weval (CState.ext_trans h1.1 h14) x hx _ (hgp_lt (m + 1 + g) (by dsimp [g]; cases col <;> simp <;> omega)),
          CState.ext_weval (CState.ext_trans h1.1 h15) x hx _ (hgp_lt (m + 2) (by omega)),
          CState.ext_weval (CState.ext_trans h1.1 h15) x hx _ (hgp_lt (m + 2 - g) (by omega)),
          CState.ext_weval (CState.ext_trans h1.1 h16) x hx _ (hgp_lt (m + 2 + g) (by dsimp [g]; cases col <;> simp <;> omega)),
          hgp_ev m (by omega), hgp_ev (m - g) (by omega), hgp_ev (m + g) (by dsimp [g]; cases col <;> simp <;> omega),
          hgp_ev (m + 1) (by omega), hgp_ev (m + 1 - g) (by omega), hgp_ev (m + 1 + g) (by dsimp [g]; cases col <;> simp <;> omega),
          hgp_ev (m + 2) (by omega), hgp_ev (m + 2 - g) (by omega), hgp_ev (m + 2 + g) (by dsimp [g]; cases col <;> simp <;> omega)]
      · intro k'
        rw [Fin.snoc_castSucc, Fin.val_castSucc, CState.ext_weval h1_13 x hx (lo k') (h1.2.2.1 k')]
        exact h1.2.2.2.2 x hx k'

def mkLocState {n_in : ℕ} (n r : ℕ) (col : Bool) (wWin : ℕ → Bool)
    (nameW : ℕ → ℕ) (cW : Fin r → ℕ → ℕ) (i0 : ℕ) :
    (t : ℕ) → CState n_in → CState n_in × (Fin (delayOp r col + 4 * (r - t) + 1) → ℕ)
  | 0, s => mkLocLayer0 n col wWin nameW i0 (delayOp r col + 4 * r + 1) s
  | j + 1, s =>
    let (s1, prev) := mkLocState n r col wWin nameW cW i0 j s
    let cw := if h : j < r then cW ⟨j, h⟩ else fun _ => 0
    mkLocStep n col wWin cw i0 j (delayOp r col + 4 * (r - j) + 1) prev (delayOp r col + 4 * (r - (j + 1)) + 1) s1

lemma mkLocState_spec {n_in : ℕ} (n r : ℕ) (col : Bool) (wWin : ℕ → Bool)
    (nameW : ℕ → ℕ) (cW : Fin r → ℕ → ℕ) (i0 : ℕ)
    (t : ℕ) (ht : t ≤ r) (s : CState n_in) (hs : s.Valid)
    (hname : ∀ u, nameW u < s.nw) (hcW : ∀ j u, cW j u < s.nw) :
    let r' := mkLocState n r col wWin nameW cW i0 t s
    s.Ext r'.1 ∧ r'.1.Valid ∧ (∀ q, r'.2 q < r'.1.nw) ∧
    r'.1.gates.length ≤ s.gates.length + (6 + 48 * t) * (7 * r + 2) ∧
    ∀ x : List Bool, x.length = n_in → ∀ q : Fin (delayOp r col + 4 * (r - t) + 1),
      r'.1.weval x (r'.2 q) =
        locState n r col wWin (fun u => s.weval x (nameW u)) (fun j u => s.weval x (cW j u)) i0 t q.val := by
  induction t generalizing s with
  | zero =>
    dsimp only [mkLocState]
    have h0 := mkLocLayer0_spec n col wWin nameW i0 (delayOp r col + 4 * r + 1) s hs hname
    have hle : delayOp r col + 4 * r + 1 ≤ 7 * r + 2 := by dsimp [delayOp]; cases col <;> simp <;> omega
    refine ⟨h0.1, h0.2.1, h0.2.2.1, by have := h0.2.2.2.1; nlinarith, ?_⟩
    intro x hx q
    exact h0.2.2.2.2 x hx q
  | succ j ih =>
    dsimp only [mkLocState]
    have h1 := ih (by omega) s hs hname hcW
    set s1 := (mkLocState n r col wWin nameW cW i0 j s).1
    set prev := (mkLocState n r col wWin nameW cW i0 j s).2
    have hQ : delayOp r col + 4 * (r - (j + 1)) + 1 + 4 ≤ delayOp r col + 4 * (r - j) + 1 := by omega
    have hjr : j < r := by omega
    have hcw_s1 : ∀ u, (if h : j < r then cW ⟨j, h⟩ else fun _ => 0) u < s1.nw := by
      intro u; rw [dif_pos hjr]; exact lt_of_lt_of_le (hcW ⟨j, hjr⟩ u) (CState.ext_nw h1.1)
    have h2 := mkLocStep_spec n col wWin (if h : j < r then cW ⟨j, h⟩ else fun _ => 0) i0 j
      (delayOp r col + 4 * (r - j) + 1) (delayOp r col + 4 * (r - (j + 1)) + 1) hQ prev s1 h1.2.1 h1.2.2.1 hcw_s1
    have hle : delayOp r col + 4 * (r - (j + 1)) + 1 ≤ 7 * r + 2 := by dsimp [delayOp]; cases col <;> simp <;> omega
    refine ⟨CState.ext_trans h1.1 h2.1, h2.2.1, h2.2.2.1, ?_, ?_⟩
    · have := h1.2.2.2.1; have := h2.2.2.2.1; dsimp only [s1] at *; nlinarith
    · intro x hx q
      rw [h2.2.2.2.2 x hx q]
      dsimp only [locState]
      rw [dif_pos hjr, dif_pos hjr, CState.ext_weval h1.1 x hx _ (hcW ⟨j, hjr⟩ _)]
      have hxv : ∀ u ≤ q.val + 4,
          (if h : u < delayOp r col + 4 * (r - j) + 1 then s1.weval x (prev ⟨u, h⟩) else false) =
            locState n r col wWin (fun u => s.weval x (nameW u)) (fun j u => s.weval x (cW j u)) i0 j u := by
        intro u hu
        have hu_lt : u < delayOp r col + 4 * (r - j) + 1 := by omega
        rw [dif_pos hu_lt]
        exact h1.2.2.2.2 x hx ⟨u, hu_lt⟩
      have hsub : ∀ δ ≤ 2,
          (let g := if col then 2 else 1
           (if h : q.val + δ < delayOp r col + 4 * (r - j) + 1 then s1.weval x (prev ⟨q.val + δ, h⟩) else false) =
             locState n r col wWin (fun u => s.weval x (nameW u)) (fun j u => s.weval x (cW j u)) i0 j (q.val + δ) ∧
           (if h : q.val + δ - g < delayOp r col + 4 * (r - j) + 1 then s1.weval x (prev ⟨q.val + δ - g, h⟩) else false) =
             locState n r col wWin (fun u => s.weval x (nameW u)) (fun j u => s.weval x (cW j u)) i0 j (q.val + δ - g) ∧
           (if h : q.val + δ + g < delayOp r col + 4 * (r - j) + 1 then s1.weval x (prev ⟨q.val + δ + g, h⟩) else false) =
             locState n r col wWin (fun u => s.weval x (nameW u)) (fun j u => s.weval x (cW j u)) i0 j (q.val + δ + g)) := by
        intro δ hδ
        refine ⟨hxv _ (by omega), hxv _ (by cases col <;> simp <;> omega), hxv _ (by cases col <;> simp <;> omega)⟩
      have hs0 := hsub 0 (by omega); simp only [add_zero] at hs0
      have hs1 := hsub 1 (by omega)
      have hs2 := hsub 2 (by omega)
      rw [hs0.1, hs0.2.1, hs0.2.2, hs1.1, hs1.2.1, hs1.2.2, hs2.1, hs2.2.1, hs2.2.2]

def mkLocSensorWire {n_in : ℕ} (n r d : ℕ)
    (nrW ncW : ℕ → ℕ) (crW ccW : Fin r → ℕ → ℕ) (bankW : Fin n → ℕ)
    (i : Fin n) (v : Fin (2 ^ d)) (b : Bool) (s : CState n_in) : CState n_in × ℕ :=
  let wWin := fun idx => if idx < d then v.val.testBit idx else b
  let (s1, arrT) := mkLocState n r true wWin ncW ccW i.val r s
  let wT := arrT ⟨delayOp r true, by omega⟩
  let (s2, arrF) := mkLocState n r false wWin nrW crW i.val r s1
  let wF := arrF ⟨delayOp r false, by omega⟩
  mkIte s2 (bankW i) wT wF

lemma mkLocSensorWire_spec {n_in : ℕ} (n r d : ℕ)
    (nrW ncW : ℕ → ℕ) (crW ccW : Fin r → ℕ → ℕ) (bankW : Fin n → ℕ)
    (i : Fin n) (v : Fin (2 ^ d)) (b : Bool) (s : CState n_in) (hs : s.Valid)
    (hnr : ∀ u, nrW u < s.nw) (hnc : ∀ u, ncW u < s.nw)
    (hcr : ∀ j u, crW j u < s.nw) (hcc : ∀ j u, ccW j u < s.nw) (hbW : bankW i < s.nw) :
    let res := mkLocSensorWire n r d nrW ncW crW ccW bankW i v b s
    s.Ext res.1 ∧ res.1.Valid ∧ res.2 < res.1.nw ∧
    res.1.gates.length ≤ s.gates.length + 2 * (6 + 48 * r) * (7 * r + 2) + 4 ∧
    ∀ x : List Bool, x.length = n_in →
      res.1.weval x res.2 =
        locSensor n r d (s.weval x (bankW i))
          (fun u => s.weval x (if s.weval x (bankW i) then ncW u else nrW u))
          (fun j u => s.weval x (if s.weval x (bankW i) then ccW j u else crW j u))
          i.val v b := by
  dsimp only [mkLocSensorWire]
  let wWin := fun idx => if idx < d then v.val.testBit idx else b
  have h1 := mkLocState_spec n r true wWin ncW ccW i.val r le_rfl s hs hnc hcc
  set s1 := (mkLocState n r true wWin ncW ccW i.val r s).1
  set arrT := (mkLocState n r true wWin ncW ccW i.val r s).2
  have h2 := mkLocState_spec n r false wWin nrW crW i.val r le_rfl s1 h1.2.1
    (fun u => lt_of_lt_of_le (hnr u) (CState.ext_nw h1.1))
    (fun j u => lt_of_lt_of_le (hcr j u) (CState.ext_nw h1.1))
  set s2 := (mkLocState n r false wWin nrW crW i.val r s1).1
  set arrF := (mkLocState n r false wWin nrW crW i.val r s1).2
  have h02 : s.Ext s2 := CState.ext_trans h1.1 h2.1
  have h3 := mkIte_spec s2 h2.2.1 (bankW i) (arrT ⟨delayOp r true, by omega⟩) (arrF ⟨delayOp r false, by omega⟩)
    (lt_of_lt_of_le hbW (CState.ext_nw h02))
    (lt_of_lt_of_le (h1.2.2.1 _) (CState.ext_nw h2.1)) (h2.2.2.1 _)
  refine ⟨CState.ext_trans h02 h3.1, h3.2.1, h3.2.2.1,
    by have := h1.2.2.2.1; have := h2.2.2.2.1; have := h3.2.2.2.1; dsimp only [s1, s2] at *; nlinarith, ?_⟩
  intro x hx
  rw [h3.2.2.2.2 x hx, CState.ext_weval h02 x hx (bankW i) hbW,
    CState.ext_weval h2.1 x hx _ (h1.2.2.1 _), h1.2.2.2.2 x hx, h2.2.2.2.2 x hx]
  have hnr_ext : (fun u => s1.weval x (nrW u)) = (fun u => s.weval x (nrW u)) :=
    funext (fun u => CState.ext_weval h1.1 x hx (nrW u) (hnr u))
  have hcr_ext : (fun j u => s1.weval x (crW j u)) = (fun j u => s.weval x (crW j u)) :=
    funext (fun j => funext (fun u => CState.ext_weval h1.1 x hx (crW j u) (hcr j u)))
  rw [hnr_ext, hcr_ext]
  cases s.weval x (bankW i) <;> rfl

def mkValidAux {n_in : ℕ} (r d : ℕ) (bankW : ℕ → ℕ) : (m : ℕ) → CState n_in → CState n_in × ℕ
  | 0, s => mkConst s true
  | m + 1, s =>
    let (s1, acc) := mkValidAux r d bankW m s
    let (s2, cT) := mkConst s1 (decide (reachOp r true ≤ d))
    let (s3, cF) := mkConst s2 (decide (reachOp r false ≤ d))
    let (s4, ok) := mkIte s3 (bankW m) cT cF
    mkAnd s4 acc ok

lemma mkValidAux_spec {n_in : ℕ} (r d : ℕ) (bankW : ℕ → ℕ) (m : ℕ)
    (s : CState n_in) (hs : s.Valid) (hbW : ∀ i < m, bankW i < s.nw) :
    let res := mkValidAux r d bankW m s
    s.Ext res.1 ∧ res.1.Valid ∧ res.2 < res.1.nw ∧
    res.1.gates.length = s.gates.length + 7 * m + 1 ∧
    ∀ x : List Bool, x.length = n_in →
      res.1.weval x res.2 = decide (∀ i < m, reachOp r (s.weval x (bankW i)) ≤ d) := by
  induction m generalizing s with
  | zero =>
    have h0 := mkConst_spec s hs true
    refine ⟨h0.1, h0.2.1, h0.2.2.1, by simp [mkValidAux, h0.2.2.2.1], ?_⟩
    intro x hx; simp [mkValidAux, h0.2.2.2.2 x hx]
  | succ m ih =>
    dsimp only [mkValidAux]
    have h1 := ih s hs (fun i hi => hbW i (by omega))
    set s1 := (mkValidAux r d bankW m s).1; set acc := (mkValidAux r d bankW m s).2
    have h2 := mkConst_spec s1 h1.2.1 (decide (reachOp r true ≤ d))
    set s2 := (mkConst s1 (decide (reachOp r true ≤ d))).1; set cT := (mkConst s1 (decide (reachOp r true ≤ d))).2
    have h3 := mkConst_spec s2 h2.2.1 (decide (reachOp r false ≤ d))
    set s3 := (mkConst s2 (decide (reachOp r false ≤ d))).1; set cF := (mkConst s2 (decide (reachOp r false ≤ d))).2
    have h03 : s.Ext s3 := CState.ext_trans h1.1 (CState.ext_trans h2.1 h3.1)
    have h4 := mkIte_spec s3 h3.2.1 (bankW m) cT cF
      (lt_of_lt_of_le (hbW m (by omega)) (CState.ext_nw h03))
      (lt_of_lt_of_le h2.2.2.1 (CState.ext_nw h3.1)) h3.2.2.1
    set s4 := (mkIte s3 (bankW m) cT cF).1; set ok := (mkIte s3 (bankW m) cT cF).2
    have h14 : s1.Ext s4 := CState.ext_trans h2.1 (CState.ext_trans h3.1 h4.1)
    have h5 := mkAnd_spec s4 h4.2.1 acc ok (lt_of_lt_of_le h1.2.2.1 (CState.ext_nw h14)) h4.2.2.1
    refine ⟨CState.ext_trans h1.1 (CState.ext_trans h14 h5.1), h5.2.1, h5.2.2.1,
      by have := h1.2.2.2.1; have := h2.2.2.2.1; have := h3.2.2.2.1; have := h4.2.2.2.1; have := h5.2.2.2.1
         dsimp only [s1, s2, s3, s4] at *; omega, ?_⟩
    intro x hx
    rw [h5.2.2.2.2 x hx, CState.ext_weval h14 x hx acc h1.2.2.1, h1.2.2.2.2 x hx,
      h4.2.2.2.2 x hx, CState.ext_weval h03 x hx (bankW m) (hbW m (by omega)),
      CState.ext_weval h3.1 x hx cT h2.2.2.1, h2.2.2.2.2 x hx, h3.2.2.2.2 x hx]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hprev, hlast⟩ i hi
      by_cases him : i < m
      · exact hprev i him
      · have : i = m := by omega
        subst this
        cases hb : s.weval x (bankW i) <;> simp [hb] at hlast ⊢ <;> exact hlast
    · intro hall
      refine ⟨fun i hi => hall i (by omega), ?_⟩
      have hm := hall m (by omega)
      cases hb : s.weval x (bankW m) <;> simp [hb] at hm ⊢ <;> exact hm

def nextWin (d : ℕ) (hd : 0 < d) (v : Fin (2 ^ d)) (b : Bool) : Fin (2 ^ d) :=
  ⟨v.val / 2 + if b then 2 ^ (d - 1) else 0, by
    have hv := v.isLt
    have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by
      conv_lhs => rw [← Nat.sub_add_cancel hd, pow_succ]
    have hdiv : v.val / 2 < 2 ^ (d - 1) := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    split_ifs <;> omega⟩

lemma nextWin_testBit (d : ℕ) (hd : 0 < d) (v : Fin (2 ^ d)) (b : Bool) (t : ℕ) (ht : t < d) :
    (nextWin d hd v b).val.testBit t = if t + 1 < d then v.val.testBit (t + 1) else b := by
  dsimp only [nextWin]
  have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by
    conv_lhs => rw [← Nat.sub_add_cancel hd, pow_succ]
  have hdiv : v.val / 2 < 2 ^ (d - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; have := v.isLt; omega
  by_cases hlt : t + 1 < d
  · simp only [hlt, ↓reduceIte]
    have ht' : t < d - 1 := by omega
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, Nat.testBit_div_two]
    · simp only [↓reduceIte]
      rw [Nat.add_comm, Nat.testBit_two_pow_add_gt ht', Nat.testBit_div_two]
  · have hteq : t = d - 1 := by omega
    subst hteq
    simp only [hlt, ↓reduceIte]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      exact Nat.testBit_lt_two_pow hdiv
    · simp only [↓reduceIte]
      rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hdiv]; rfl

def winOf (k d : ℕ) (w : Fin (2 ^ k)) (pos : ℕ) : Fin (2 ^ d) :=
  ⟨∑ t : Fin d, if w.val.testBit ((pos + t.val) % k) then 2 ^ t.val else 0, by
    have hsum : ∀ (m : ℕ) (f : Fin m → Bool), (∑ t : Fin m, if f t then 2 ^ t.val else 0) < 2 ^ m := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro f
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        have h1 := ih (fun t => f t.castSucc)
        have h2 : (if f (Fin.last m) = true then 2 ^ m else 0) ≤ 2 ^ m := by split_ifs <;> omega
        have h3 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
        omega
    exact hsum d _⟩

lemma winOf_testBit (k d : ℕ) (w : Fin (2 ^ k)) (pos t : ℕ) (ht : t < d) :
    (winOf k d w pos).val.testBit t = w.val.testBit ((pos + t) % k) := by
  dsimp only [winOf]
  have hgen : ∀ (m : ℕ) (f : Fin m → Bool) (i : ℕ) (hi : i < m),
      (∑ j : Fin m, if f j then 2 ^ j.val else 0).testBit i = f ⟨i, hi⟩ := by
    intro m
    induction m with
    | zero => intro _ _ hi; omega
    | succ m ih =>
      intro f i hi
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      set lo := ∑ j : Fin m, if f j.castSucc = true then 2 ^ j.val else 0
      have hlo : lo < 2 ^ m := by
        have hsum : ∀ (m' : ℕ) (g : Fin m' → Bool), (∑ j : Fin m', if g j then 2 ^ j.val else 0) < 2 ^ m' := by
          intro m'; induction m' with
          | zero => intro _; simp
          | succ m' ih' =>
            intro g; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
            have := ih' (fun j => g j.castSucc); have : 2 ^ (m' + 1) = 2 ^ m' + 2 ^ m' := by rw [pow_succ]; omega
            split_ifs <;> omega
        exact hsum m _
      by_cases him : i = m
      · subst him
        cases hf : f (Fin.last i)
        · simp [Nat.testBit_lt_two_pow hlo]; exact hf.symm.symm
        · simp only [↓reduceIte]
          rw [Nat.add_comm lo, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlo]
          exact hf.symm
      · have hilt : i < m := by omega
        cases hf : f (Fin.last m)
        · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
          exact ih (fun j => f j.castSucc) i hilt
        · simp only [↓reduceIte]
          rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hilt]
          exact ih (fun j => f j.castSucc) i hilt
  exact hgen d (fun j => w.val.testBit ((pos + j.val) % k)) t ht

lemma nextWin_winOf (k d : ℕ) (hd : 0 < d) (w : Fin (2 ^ k)) (pos : ℕ) :
    nextWin d hd (winOf k d w pos) (w.val.testBit ((pos + d) % k)) = winOf k d w (pos + 1) := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < d
  · rw [nextWin_testBit d hd _ _ t ht, winOf_testBit k d w (pos + 1) t ht]
    by_cases hlt : t + 1 < d
    · simp only [hlt, ↓reduceIte, winOf_testBit k d w pos (t + 1) hlt]
      congr 2; omega
    · simp only [hlt, ↓reduceIte]
      have : pos + 1 + t = pos + d := by omega
      rw [this]
  · have h1 : (nextWin d hd (winOf k d w pos) (w.val.testBit ((pos + d) % k))).val < 2 ^ t :=
      lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : (winOf k d w (pos + 1)).val < 2 ^ t :=
      lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

def evolve (n d : ℕ) (hd : 0 < d) (v : Fin (2 ^ d)) (bits : Fin n → Bool) : ℕ → Fin (2 ^ d)
  | 0 => v
  | i + 1 => nextWin d hd (evolve n d hd v bits i) (if h : i < n then bits ⟨i, h⟩ else false)

lemma evolve_winOf (p n d : ℕ) (hd : 0 < d) (w : Fin (2 ^ (p * n))) (a : Fin p) (i : ℕ) (hi : i ≤ n) :
    evolve n d hd (winOf (p * n) d w (a.val * n))
      (fun j : Fin n => w.val.testBit ((a.val * n + j.val + d) % (p * n))) i =
      winOf (p * n) d w (a.val * n + i) := by
  induction i with
  | zero => simp [evolve]
  | succ m ih =>
    dsimp only [evolve]
    have hm : m < n := by omega
    rw [dite_cond_eq_true (eq_true hm), ih (by omega)]
    exact nextWin_winOf (p * n) d hd w (a.val * n + m)

lemma evolve_n_testBit (n d : ℕ) (hd : 0 < d) (hdn : d < n) (v : Fin (2 ^ d))
    (bits : Fin n → Bool) (t : ℕ) (ht : t < d) :
    (evolve n d hd v bits n).val.testBit t = bits ⟨n - d + t, by omega⟩ := by
  have hgen : ∀ (m : ℕ) (hm : m ≤ n) (t : ℕ) (ht : t < d),
      (evolve n d hd v bits m).val.testBit t =
        if m + t < d then v.val.testBit (m + t) else bits ⟨m + t - d, by omega⟩ := by
    intro m
    induction m with
    | zero =>
      intro _ t ht
      simp [evolve, ht]
    | succ m ih =>
      intro hm t ht
      dsimp only [evolve]
      have hmlt : m < n := by omega
      rw [nextWin_testBit d hd _ _ t ht]
      by_cases hlt : t + 1 < d
      · simp only [hlt, ↓reduceIte, ih (by omega) (t + 1) hlt]
        have hcond : (m + (t + 1) < d) ↔ (m + 1 + t < d) := by omega
        by_cases hc : m + (t + 1) < d
        · have hc' : m + 1 + t < d := by omega
          simp only [hc, hc', ↓reduceIte]; congr 1; omega
        · have hc' : ¬ (m + 1 + t < d) := by omega
          simp only [hc, hc', ↓reduceIte]; congr 1; ext; dsimp; omega
      · have hteq : t = d - 1 := by omega
        have hnot : ¬ (m + 1 + t < d) := by omega
        simp only [hlt, hnot, ↓reduceIte]
        rw [dite_cond_eq_true (eq_true hmlt)]
        congr 1; ext; dsimp; omega
  have h := hgen n le_rfl t ht
  have hnot : ¬ (n + t < d) := by omega
  simp only [hnot, ↓reduceIte] at h
  rw [h]; congr 1; ext; dsimp; omega

def allHists : (M S : ℕ) → List (Fin M → ℕ)
  | 0, 0 => [Fin.elim0]
  | 0, _ + 1 => []
  | M + 1, S =>
    (List.range (S + 1)).flatMap fun c =>
      (allHists M (S - c)).map fun h => Fin.snoc h c

lemma mem_allHists (M S : ℕ) (h : Fin M → ℕ) :
    h ∈ allHists M S ↔ ∑ i : Fin M, h i = S := by
  induction M generalizing S with
  | zero =>
    cases S with
    | zero =>
      simp only [allHists, List.mem_singleton, Finset.univ_eq_empty, Finset.sum_empty, iff_true]
      funext i; exact Fin.elim0 i
    | succ S =>
      simp [allHists]
  | succ M ih =>
    simp only [allHists, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨c, hc, h', hh', rfl⟩
      rw [ih] at hh'
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      omega
    · intro hsum
      rw [Fin.sum_univ_castSucc] at hsum
      refine ⟨h (Fin.last M), by omega, fun i => h i.castSucc, ?_, ?_⟩
      · rw [ih]; omega
      · funext i
        refine Fin.lastCases (by simp [Fin.snoc_last]) (fun j => by simp [Fin.snoc_castSucc]) i

lemma nodup_allHists (M S : ℕ) : (allHists M S).Nodup := by
  induction M generalizing S with
  | zero =>
    cases S <;> simp [allHists]
  | succ M ih =>
    dsimp only [allHists]
    rw [List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · intro c _
      apply List.Nodup.map _ (ih (S - c))
      intro h₁ h₂ heq
      funext i
      have := congrFun heq i.castSucc
      simpa [Fin.snoc_castSucc] using this
    · refine List.Pairwise.imp (fun {c₁ c₂} hne => ?_) List.nodup_range
      intro h h1 h2
      rw [List.mem_map] at h1 h2
      rcases h1 with ⟨_, _, rfl⟩
      rcases h2 with ⟨h', _, heq⟩
      have := congrFun heq (Fin.last M)
      simp only [Fin.snoc_last] at this
      exact hne this.symm

lemma length_allHists (M S : ℕ) (hM : 1 ≤ M) :
    (allHists M S).length = (S + M - 1).choose S := by
  induction M generalizing S with
  | zero => omega
  | succ M ih =>
    cases M with
    | zero =>
      dsimp only [allHists]
      rw [List.length_flatMap]
      have h1 : ∀ c ∈ List.range (S + 1),
          ((allHists 0 (S - c)).map (fun h => Fin.snoc (α := fun _ => ℕ) h c)).length = if c = S then 1 else 0 := by
        intro c hc
        rw [List.mem_range] at hc
        rw [List.length_map]
        by_cases hcs : c = S
        · subst hcs; simp [allHists]
        · have hpos : S - c = (S - c - 1) + 1 := by omega
          rw [hpos]; simp [allHists, hcs]
      rw [List.map_congr_left h1]
      have hsum : ((List.range (S + 1)).map fun c => if c = S then 1 else 0).sum = 1 := by
        rw [List.range_succ, List.map_append, List.sum_append]
        have h0 : ((List.range S).map fun c => if c = S then 1 else 0).sum = 0 := by
          apply List.sum_eq_zero
          intro x hx; rw [List.mem_map] at hx
          rcases hx with ⟨c, hc, rfl⟩
          rw [List.mem_range] at hc
          simp [Nat.ne_of_lt hc]
        simp [h0]
      rw [hsum]; simp
    | succ M' =>
      rw [allHists, List.length_flatMap]
      have hlen : ∀ c ∈ List.range (S + 1),
          ((allHists (M' + 1) (S - c)).map (fun h => Fin.snoc (α := fun _ => ℕ) h c)).length =
            (S - c + M').choose (S - c) := by
        intro c _
        rw [List.length_map, ih (S - c) (by omega)]
        simp
      rw [List.map_congr_left hlen]

      have hstick : ∀ s : ℕ, ((List.range (s + 1)).map fun c => (s - c + M').choose (s - c)).sum =
          (s + M' + 1).choose s := by
        intro s
        induction s with
        | zero => simp
        | succ s ihs =>
          rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
          have hsub : ((List.range (s + 1)).map ((fun c => (s + 1 - c + M').choose (s + 1 - c)) ∘ Nat.succ)) =
              (List.range (s + 1)).map (fun c => (s - c + M').choose (s - c)) := by
            apply List.map_congr_left
            intro c _; simp [Function.comp]
          rw [hsub, ihs]
          simp only [Nat.sub_zero]
          have h1 : s + 1 + M' = (s + M') + 1 := by omega
          have h2 : s + 1 + M' + 1 = (s + M' + 1) + 1 := by omega
          rw [h2, Nat.choose_succ_succ, h1, Nat.add_comm]
      simpa [Nat.add_assoc] using hstick S

def pairIdx (D : ℕ) (v w : Fin D) : Fin (D * D) :=
  ⟨v.val * D + w.val, by
    have hv := v.isLt; have hw := w.isLt
    have : v.val * D + w.val < (v.val + 1) * D := by rw [Nat.add_mul, one_mul]; omega
    exact lt_of_lt_of_le this (Nat.mul_le_mul_right D (by omega))⟩

lemma pairIdx_injective (D : ℕ) (v₁ w₁ v₂ w₂ : Fin D)
    (h : pairIdx D v₁ w₁ = pairIdx D v₂ w₂) : v₁ = v₂ ∧ w₁ = w₂ := by
  have heq : v₁.val * D + w₁.val = v₂.val * D + w₂.val := congrArg Fin.val h
  have hD : 0 < D := Nat.pos_of_ne_zero (by intro h0; subst h0; exact Fin.elim0 v₁)
  have hv : v₁.val = v₂.val := by
    have h1 := congrArg (· / D) heq
    rw [Nat.mul_comm v₁.val, Nat.mul_comm v₂.val, Nat.mul_add_div hD, Nat.mul_add_div hD,
      Nat.div_eq_of_lt w₁.isLt, Nat.div_eq_of_lt w₂.isLt] at h1
    omega
  have hw : w₁.val = w₂.val := by rw [hv] at heq; omega
  exact ⟨Fin.ext hv, Fin.ext hw⟩

def pathCount (D : ℕ) : (a0 : ℕ) → Fin D → Fin D → (Fin (D * D) → ℕ) → ℕ
  | 0, s0, u_tag, h => if s0 = u_tag ∧ ∀ idx, h idx = 0 then 1 else 0
  | m + 1, s0, u_tag, h =>
    ∑ prev : Fin D,
      let idx := pairIdx D prev u_tag
      if 0 < h idx then
        pathCount D m s0 prev (Function.update h idx (h idx - 1))
      else 0

def hitLoc (p n d : ℕ) (loc : Fin n → Fin (2 ^ d) → Bool → Bool) (y : Fin n → Bool)
    (w : Fin (2 ^ (p * n))) : Prop :=
  ∀ i : Fin n,
    (List.finRange p).foldl (fun acc a =>
      xor acc (loc i (winOf (p * n) d w (a.val * n + i.val))
        (w.val.testBit ((a.val * n + i.val + d) % (p * n))))) false = y i

def prefMatch (k m : ℕ) (pref : ℕ → Bool) (w : Fin (2 ^ k)) : Prop :=
  ∀ pos, m ≤ pos → pos < k → w.val.testBit pos = pref pos

def highBit (k d : ℕ) (pref : ℕ → Bool) (s0 : Fin (2 ^ d)) (pos : ℕ) : Bool :=
  if pos < k then pref pos else s0.val.testBit (pos - k)

def highWin (k d : ℕ) (pref : ℕ → Bool) (s0 : Fin (2 ^ d)) (pos : ℕ) : Fin (2 ^ d) :=
  ⟨∑ t : Fin d, if highBit k d pref s0 (pos + t.val) then 2 ^ t.val else 0, by
    have hsum : ∀ (m : ℕ) (f : Fin m → Bool), (∑ t : Fin m, if f t then 2 ^ t.val else 0) < 2 ^ m := by
      intro m; induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro f; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
        have := ih (fun t => f t.castSucc); have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
        split_ifs <;> omega
    exact hsum d _⟩

def s0Match (m d : ℕ) (pref : ℕ → Bool) (s0 : Fin (2 ^ d)) : Bool :=
  (List.range d).all (fun t => decide (t < m) || decide (s0.val.testBit t = pref t))

def uTagMatch (a0 n r0 d : ℕ) (pref : ℕ → Bool) (u : Fin (2 ^ d)) : Bool :=
  (List.range d).all (fun t => decide (t < r0) || decide (u.val.testBit t = pref (a0 * n + t)))

def wTagOf (p n d a0 : ℕ) (pref : ℕ → Bool) (s0 : Fin (2 ^ d)) : Fin (2 ^ d) :=
  if a0 + 1 < p then highWin (p * n) d pref s0 ((a0 + 1) * n) else s0

def highPar (p n d a0 : ℕ) (loc : Fin n → Fin (2 ^ d) → Bool → Bool)
    (pref : ℕ → Bool) (s0 : Fin (2 ^ d)) (i : Fin n) : Bool :=
  (List.finRange p).foldl (fun acc a =>
    if a0 < a.val then
      xor acc (loc i (highWin (p * n) d pref s0 (a.val * n + i.val))
        (highBit (p * n) d pref s0 (a.val * n + i.val + d)))
    else acc) false

def stepHist (d : ℕ) (hd : 0 < d) (rem : ℕ) (hrem : rem < 2 ^ d * 2 ^ d)
    (h : Fin (rem + 1 + 2 ^ d * 2 ^ d) → ℕ) (c0 : ℕ) : Fin (rem + 2 ^ d * 2 ^ d) → ℕ :=
  let D := 2 ^ d
  let v : Fin D := ⟨rem / D, Nat.div_lt_of_lt_mul hrem⟩
  let w : Fin D := ⟨rem % D, Nat.mod_lt _ (by positivity)⟩
  let c := h ⟨rem, by omega⟩
  let c1 := c - c0
  let i0 := rem + (pairIdx D (nextWin d hd v false) w).val
  let i1 := rem + (pairIdx D (nextWin d hd v true) w).val
  fun j =>
    (if hj : j.val < rem then h ⟨j.val, by omega⟩ else h ⟨j.val + 1, by omega⟩) +
    (if j.val = i0 then c0 else 0) +
    (if j.val = i1 then c1 else 0)

def stepPar (d : ℕ) (rem : ℕ) (hrem : rem < 2 ^ d * 2 ^ d)
    (loc_i : Fin (2 ^ d) → Bool → Bool) (c0 c1 : ℕ) : Bool :=
  let D := 2 ^ d
  let v : Fin D := ⟨rem / D, Nat.div_lt_of_lt_mul hrem⟩
  xor (decide (c0 % 2 = 1) && loc_i v false) (decide (c1 % 2 = 1) && loc_i v true)

lemma stepHist_sum (d : ℕ) (hd : 0 < d) (rem : ℕ) (hrem : rem < 2 ^ d * 2 ^ d)
    (h : Fin (rem + 1 + 2 ^ d * 2 ^ d) → ℕ) (c0 : ℕ) (hc0 : c0 ≤ h ⟨rem, by omega⟩) :
    ∑ j : Fin (rem + 2 ^ d * 2 ^ d), stepHist d hd rem hrem h c0 j = ∑ j, h j := by
  dsimp only [stepHist]
  let D := 2 ^ d
  let v : Fin D := ⟨rem / D, Nat.div_lt_of_lt_mul hrem⟩
  let w : Fin D := ⟨rem % D, Nat.mod_lt _ (by positivity)⟩
  let i0 : Fin (rem + D * D) := ⟨rem + (pairIdx D (nextWin d hd v false) w).val, by omega⟩
  let i1 : Fin (rem + D * D) := ⟨rem + (pairIdx D (nextWin d hd v true) w).val, by omega⟩
  simp only [Finset.sum_add_distrib]
  have hs0 : (∑ j : Fin (rem + D * D), if j.val = i0.val then c0 else 0) = c0 := by
    rw [Finset.sum_eq_single i0]
    · simp
    · intro j _ hne; simp [Fin.val_ne_of_ne hne]
    · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
  have hs1 : (∑ j : Fin (rem + D * D), if j.val = i1.val then h ⟨rem, by omega⟩ - c0 else 0) =
      h ⟨rem, by omega⟩ - c0 := by
    rw [Finset.sum_eq_single i1]
    · simp
    · intro j _ hne; simp [Fin.val_ne_of_ne hne]
    · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
  have hmain : (∑ j : Fin (rem + D * D), if hj : j.val < rem then h ⟨j.val, by dsimp [D] at *; omega⟩ else h ⟨j.val + 1, by dsimp [D] at *; omega⟩) +
      h ⟨rem, by dsimp [D] at *; omega⟩ = ∑ j : Fin (rem + 1 + D * D), h j := by
    let p_rem : Fin (rem + 1 + D * D) := ⟨rem, by omega⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p_rem)]
    rw [Nat.add_comm]
    congr 1
    refine Finset.sum_bij (fun j _ => if hj : j.val < rem then ⟨j.val, by dsimp [D] at *; omega⟩ else ⟨j.val + 1, by dsimp [D] at *; omega⟩) ?_ ?_ ?_ ?_
    · intro j _
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      split_ifs <;> intro heq <;> have := congrArg Fin.val heq <;> dsimp [p_rem] at this <;> omega
    · intro j₁ _ j₂ _ heq
      have hv := congrArg Fin.val heq
      split_ifs at hv <;> dsimp at hv <;> apply Fin.ext <;> omega
    · intro j hj
      rw [Finset.mem_erase] at hj
      have hne : j.val ≠ rem := fun h' => hj.1 (Fin.ext h')
      by_cases hlt : j.val < rem
      · refine ⟨⟨j.val, by dsimp [D] at *; omega⟩, Finset.mem_univ _, ?_⟩
        simp [hlt]
      · refine ⟨⟨j.val - 1, by dsimp [D] at *; omega⟩, Finset.mem_univ _, ?_⟩
        have hnot : ¬ (j.val - 1 < rem) := by omega
        simp only [hnot, ↓reduceDIte]
        apply Fin.ext; dsimp; omega
    · intro j _; split_ifs <;> rfl
  rw [hs0, hs1]
  dsimp [D] at *
  omega

def dpBinStep (d : ℕ) (hd : 0 < d) (a0 : ℕ) (loc_i : Fin (2 ^ d) → Bool → Bool)
    (rem : ℕ) (hrem : rem < 2 ^ d * 2 ^ d)
    (tab : (Fin (rem + 1 + 2 ^ d * 2 ^ d) → ℕ) → Bool → ℕ) :
    (Fin (rem + 2 ^ d * 2 ^ d) → ℕ) → Bool → ℕ :=
  (allHists (rem + 1 + 2 ^ d * 2 ^ d) a0).foldl (fun acc h =>
    let c := h ⟨rem, by omega⟩
    (List.range (c + 1)).foldl (fun acc' c0 =>
      let h' := stepHist d hd rem hrem h c0
      let mult := c.choose c0
      let pf := stepPar d rem hrem loc_i c0 (c - c0)
      fun hh p => acc' hh p + if hh = h' then mult * tab h (xor p pf) else 0
    ) acc
  ) (fun _ _ => 0)

def dpInnerAux (d : ℕ) (hd : 0 < d) (a0 : ℕ) (loc_i : Fin (2 ^ d) → Bool → Bool) :
    (rem : ℕ) → (rem ≤ 2 ^ d * 2 ^ d) →
    ((Fin (rem + 2 ^ d * 2 ^ d) → ℕ) → Bool → ℕ) →
    (Fin (2 ^ d * 2 ^ d) → ℕ) → Bool → ℕ
  | 0, _, tab => fun h p => tab (fun j => h ⟨j.val, by omega⟩) p
  | rem + 1, hle, tab =>
    dpInnerAux d hd a0 loc_i rem (by omega)
      (dpBinStep d hd a0 loc_i rem (by omega) tab)

def liftHist (D : ℕ) (h : Fin (D * D) → ℕ) : Fin (D * D + D * D) → ℕ :=
  fun j => if hj : j.val < D * D then h ⟨j.val, hj⟩ else 0

def dpResidueStep (p n d : ℕ) (hd : 0 < d) (a0 r0 : ℕ)
    (loc_i : Fin (2 ^ d) → Bool → Bool) (pref : ℕ → Bool) (s0 : Fin (2 ^ d))
    (i : Fin n) (targetPar : Bool)
    (dp : (Fin (2 ^ d * 2 ^ d) → ℕ) → Fin (2 ^ d) → ℕ) :
    (Fin (2 ^ d * 2 ^ d) → ℕ) → Fin (2 ^ d) → ℕ :=
  let D := 2 ^ d
  let w_tag := wTagOf p n d a0 pref s0
  let bitAllowed : Bool → Bool := fun b =>
    if i.val + d < r0 then true
    else if i.val + d < n then decide (b = pref (a0 * n + i.val + d))
    else decide (b = w_tag.val.testBit (i.val + d - n))

  let evolved : Fin D → (Fin (D * D) → ℕ) → Bool → ℕ := fun v_tag =>
    let initTab : (Fin (D * D + D * D) → ℕ) → Bool → ℕ := fun H par =>
      if par = false ∧ ∀ j : Fin (D * D), H ⟨D * D + j.val, by dsimp [D]; omega⟩ = 0 then
        dp (fun j => H ⟨j.val, by dsimp [D]; omega⟩) v_tag
      else 0
    dpInnerAux d hd a0 loc_i (D * D) le_rfl initTab
  fun h' v_tag' =>
    ∑ v_tag : Fin D, ∑ b : Bool,
      if bitAllowed b = true ∧ nextWin d hd v_tag b = v_tag' then
        evolved v_tag h' (xor targetPar (loc_i v_tag b))
      else 0

def dpRunResidues (p n d : ℕ) (hd : 0 < d) (a0 r0 : ℕ)
    (loc : Fin n → Fin (2 ^ d) → Bool → Bool) (y : Fin n → Bool)
    (pref : ℕ → Bool) (s0 : Fin (2 ^ d)) :
    (i : ℕ) → (i ≤ n) →
    ((Fin (2 ^ d * 2 ^ d) → ℕ) → Fin (2 ^ d) → ℕ)
  | 0, _ => fun h u_tag =>
    if uTagMatch a0 n r0 d pref u_tag = true then pathCount (2 ^ d) a0 s0 u_tag h else 0
  | i + 1, hi =>
    let prev := dpRunResidues p n d hd a0 r0 loc y pref s0 i (by omega)
    let ifin : Fin n := ⟨i, hi⟩
    let tpar := xor (y ifin) (highPar p n d a0 loc pref s0 ifin)
    dpResidueStep p n d hd a0 r0 (loc ifin) pref s0 ifin tpar prev

def isDiagHist (D : ℕ) (h : Fin (D * D) → ℕ) : Bool :=
  (List.finRange D).all fun v =>
    (List.finRange D).all fun w =>
      decide (v = w) || decide (h (pairIdx D v w) = 0)

def dpPrefixCount (p n d : ℕ) (hd : 0 < d) (m : ℕ)
    (loc : Fin n → Fin (2 ^ d) → Bool → Bool) (y : Fin n → Bool)
    (pref : ℕ → Bool) : ℕ :=
  let a0 := m / n
  let r0 := m % n
  let D := 2 ^ d
  ∑ s0 : Fin D,
    if s0Match m d pref s0 = true then
      let finalDp := dpRunResidues p n d hd a0 r0 loc y pref s0 n le_rfl
      let w_tag := wTagOf p n d a0 pref s0
      ((allHists (D * D) a0).map fun h =>
        if isDiagHist D h = true then finalDp h w_tag else 0).sum
    else 0

lemma foldl_xor_eq_parity {m : ℕ} (f : Fin m → Bool) :
    (List.finRange m).foldl (fun acc a => xor acc (f a)) false =
      decide ((Finset.univ.filter (fun a : Fin m => f a = true)).card % 2 = 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hfr : List.finRange (m + 1) = (List.finRange m).map Fin.castSucc ++ [Fin.last m] := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.getElem_finRange]
        by_cases him : i < m
        · rw [List.getElem_append_left (by simp [him]), List.getElem_map, List.getElem_finRange]
          rfl
        · have heq : i = m := by simp at hi1; omega
          subst heq
          rw [List.getElem_append_right (by simp)]
          simp; rfl
    rw [hfr, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_map, ih]
    have hcard : (Finset.univ.filter (fun a : Fin (m + 1) => f a = true)).card =
        (Finset.univ.filter (fun a : Fin m => f a.castSucc = true)).card +
        if f (Fin.last m) = true then 1 else 0 := by
      have hsum : ∀ (k : ℕ) (g : Fin k → Bool),
          (Finset.univ.filter (fun a : Fin k => g a = true)).card =
            ∑ a : Fin k, if g a = true then 1 else 0 := by
        intro k g; simp [Finset.sum_boole]
      rw [hsum, hsum, Fin.sum_univ_castSucc]
    rw [hcard]
    cases f (Fin.last m) <;> simp <;>
      cases Nat.mod_two_eq_zero_or_one (Finset.univ.filter (fun a : Fin m => f a.castSucc = true)).card with
      | inl h0 => simp [h0, Nat.add_mod]
      | inr h1 => simp [h1, Nat.add_mod]

lemma pathCount_spec (D a0 : ℕ) (s0 u_tag : Fin D) (h : Fin (D * D) → ℕ) :
    pathCount D a0 s0 u_tag h =
      (Finset.univ.filter (fun s : Fin (a0 + 1) → Fin D =>
        s 0 = s0 ∧ s (Fin.last a0) = u_tag ∧
        ∀ idx, (Finset.univ.filter (fun a : Fin a0 => pairIdx D (s a.castSucc) (s a.succ) = idx)).card = h idx)).card := by
  induction a0 generalizing u_tag h with
  | zero =>
    dsimp only [pathCount]
    by_cases hcond : s0 = u_tag ∧ ∀ idx, h idx = 0
    · rw [if_pos hcond]
      have huniq : Finset.univ.filter (fun s : Fin 1 → Fin D =>
          s 0 = s0 ∧ s (Fin.last 0) = u_tag ∧
          ∀ idx, (Finset.univ.filter (fun a : Fin 0 => pairIdx D (s a.castSucc) (s a.succ) = idx)).card = h idx) =
          {fun _ => s0} := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hs0, _, _⟩
          funext i; fin_cases i; exact hs0
        · rintro rfl
          refine ⟨rfl, hcond.1, fun idx => ?_⟩
          simp [hcond.2 idx]
      rw [huniq, Finset.card_singleton]
    · rw [if_neg hcond]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro s _ ⟨hs0, hsl, hidx⟩
      apply hcond
      refine ⟨hs0.symm.trans hsl, fun idx => ?_⟩
      have := hidx idx
      simp at this
      exact this.symm
  | succ m ih =>
    dsimp only [pathCount]

    let S := Finset.univ.filter (fun s : Fin (m + 2) → Fin D =>
      s 0 = s0 ∧ s (Fin.last (m + 1)) = u_tag ∧
      ∀ idx, (Finset.univ.filter (fun a : Fin (m + 1) => pairIdx D (s a.castSucc) (s a.succ) = idx)).card = h idx)
    have hpart : S.card = ∑ prev : Fin D, (S.filter (fun s => s (Fin.last m).castSucc = prev)).card := by
      rw [← Finset.card_biUnion (by
        intro p₁ _ p₂ _ hne
        simp only [Function.onFun, Finset.disjoint_left]
        intro s hs1 hs2
        simp only [Finset.mem_filter] at hs1 hs2
        exact hne (hs1.2.symm.trans hs2.2))]
      congr 1; ext s; simp
    rw [hpart]
    apply Finset.sum_congr rfl
    intro prev _
    let idx0 := pairIdx D prev u_tag
    by_cases hpos : 0 < h idx0
    · rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' hpos)), ih prev (Function.update h idx0 (h idx0 - 1))]
      refine Finset.card_bij (fun s _ => Fin.snoc (α := fun _ => Fin D) s u_tag) ?_ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hs ⊢
        rcases hs with ⟨hs0, hsl, hcnt⟩
        refine ⟨⟨?_, by simp [Fin.snoc_last], ?_⟩, by simp [Fin.snoc_castSucc, hsl]⟩
        · change Fin.snoc (α := fun _ => Fin D) s u_tag (0 : Fin (m + 1)).castSucc = s0
          rw [Fin.snoc_castSucc]; exact hs0
        · intro idx
          have hsplit : (Finset.univ.filter (fun a : Fin (m + 1) =>
              pairIdx D (Fin.snoc (α := fun _ => Fin D) s u_tag a.castSucc) (Fin.snoc (α := fun _ => Fin D) s u_tag a.succ) = idx)).card =
              (Finset.univ.filter (fun a : Fin m =>
                pairIdx D (s a.castSucc) (s a.succ) = idx)).card +
              if idx0 = idx then 1 else 0 := by
            have hboole : ∀ (k : ℕ) (P : Fin k → Prop) [DecidablePred P],
                (Finset.univ.filter P).card = ∑ a : Fin k, if P a then 1 else 0 := by
              intro k P _; simp [Finset.sum_boole]
            rw [hboole, hboole, Fin.sum_univ_castSucc]
            congr 1
            · apply Finset.sum_congr rfl
              intro a _
              have h2 : a.castSucc.succ = a.succ.castSucc := rfl
              rw [Fin.snoc_castSucc, h2, Fin.snoc_castSucc]
            · have h2 : (Fin.last m).succ = Fin.last (m + 1) := rfl
              rw [Fin.snoc_castSucc, h2, Fin.snoc_last, hsl]
          rw [hsplit, hcnt idx]
          by_cases heq : idx = idx0
          · subst heq; simp [Function.update_self]; omega
          · have hne : idx0 ≠ idx := Ne.symm heq
            simp [Function.update_of_ne heq, hne]
      · intro s₁ _ s₂ _ heq
        funext i
        have := congrFun heq i.castSucc
        simpa [Fin.snoc_castSucc] using this
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hs
        rcases hs with ⟨⟨hs0, hsl, hcnt⟩, hprev⟩
        refine ⟨fun i => s i.castSucc, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hs0, hprev, fun idx => ?_⟩
          have hsplit : (Finset.univ.filter (fun a : Fin (m + 1) =>
              pairIdx D (s a.castSucc) (s a.succ) = idx)).card =
              (Finset.univ.filter (fun a : Fin m =>
                pairIdx D (s a.castSucc.castSucc) (s a.succ.castSucc) = idx)).card +
              if idx0 = idx then 1 else 0 := by
            have hboole : ∀ (k : ℕ) (P : Fin k → Prop) [DecidablePred P],
                (Finset.univ.filter P).card = ∑ a : Fin k, if P a then 1 else 0 := by
              intro k P _; simp [Finset.sum_boole]
            rw [hboole, hboole, Fin.sum_univ_castSucc]
            congr 1
            have : (Fin.last m).succ = Fin.last (m + 1) := rfl
            rw [this, hprev, hsl]
          have hc := hcnt idx
          rw [hsplit] at hc
          by_cases heq : idx = idx0
          · subst heq; simp [Function.update_self] at hc ⊢; omega
          · have hne : idx0 ≠ idx := Ne.symm heq
            simp [Function.update_of_ne heq, hne] at hc ⊢; omega
        · funext i
          refine Fin.lastCases ?_ ?_ i
          · simp [Fin.snoc_last, hsl]
          · intro j; simp [Fin.snoc_castSucc]
    · rw [if_neg hpos]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro s hs hprev
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hs
      have hc := hs.2.2 idx0
      have hmem : Fin.last m ∈ Finset.univ.filter (fun a : Fin (m + 1) => pairIdx D (s a.castSucc) (s a.succ) = idx0) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have : (Fin.last m).succ = Fin.last (m + 1) := rfl
        rw [this, hprev, hs.2.1]
      have hpos' : 0 < (Finset.univ.filter (fun a : Fin (m + 1) => pairIdx D (s a.castSucc) (s a.succ) = idx0)).card :=
        Finset.card_pos.mpr ⟨Fin.last m, hmem⟩
      omega

lemma foldl_add_fn {α β : Type*} (l : List α) (f : α → β → ℕ) (init : β → ℕ) (b : β) :
    (l.foldl (fun acc a => fun x => acc x + f a x) init) b = init b + (l.map (fun a => f a b)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    omega

lemma dpBinStep_eq_sum (d : ℕ) (hd : 0 < d) (a0 : ℕ) (loc_i : Fin (2 ^ d) → Bool → Bool)
    (rem : ℕ) (hrem : rem < 2 ^ d * 2 ^ d)
    (tab : (Fin (rem + 1 + 2 ^ d * 2 ^ d) → ℕ) → Bool → ℕ)
    (h' : Fin (rem + 2 ^ d * 2 ^ d) → ℕ) (p : Bool) :
    dpBinStep d hd a0 loc_i rem hrem tab h' p =
      ∑ h ∈ (allHists (rem + 1 + 2 ^ d * 2 ^ d) a0).toFinset,
        ∑ c0 ∈ Finset.range (h ⟨rem, by omega⟩ + 1),
          if stepHist d hd rem hrem h c0 = h' then
            (h ⟨rem, by omega⟩).choose c0 * tab h (xor p (stepPar d rem hrem loc_i c0 (h ⟨rem, by omega⟩ - c0)))
          else 0 := by
  unfold dpBinStep
  have hinner : ∀ (h : Fin (rem + 1 + 2 ^ d * 2 ^ d) → ℕ)
      (acc : (Fin (rem + 2 ^ d * 2 ^ d) → ℕ) → Bool → ℕ),
      ((List.range (h ⟨rem, by omega⟩ + 1)).foldl (fun acc' c0 =>
        let hh' := stepHist d hd rem hrem h c0
        let mult := (h ⟨rem, by omega⟩).choose c0
        let pf := stepPar d rem hrem loc_i c0 (h ⟨rem, by omega⟩ - c0)
        fun hh pp => acc' hh pp + if hh = hh' then mult * tab h (xor pp pf) else 0) acc) h' p =
      acc h' p + ∑ c0 ∈ Finset.range (h ⟨rem, by omega⟩ + 1),
        if stepHist d hd rem hrem h c0 = h' then
          (h ⟨rem, by omega⟩).choose c0 * tab h (xor p (stepPar d rem hrem loc_i c0 (h ⟨rem, by omega⟩ - c0)))
        else 0 := by
    intro h acc
    have hstep := foldl_add_fn (List.range (h ⟨rem, by omega⟩ + 1))
      (fun c0 (hp : (Fin (rem + 2 ^ d * 2 ^ d) → ℕ) × Bool) =>
        if hp.1 = stepHist d hd rem hrem h c0 then
          (h ⟨rem, by omega⟩).choose c0 * tab h (xor hp.2 (stepPar d rem hrem loc_i c0 (h ⟨rem, by omega⟩ - c0)))
        else 0)
      (fun hp => acc hp.1 hp.2) (h', p)
    have hcurry : ∀ (l : List ℕ) (init : (Fin (rem + 2 ^ d * 2 ^ d) → ℕ) → Bool → ℕ),
        (l.foldl (fun acc' c0 =>
          fun hh pp => acc' hh pp + if hh = stepHist d hd rem hrem h c0 then
            (h ⟨rem, by omega⟩).choose c0 * tab h (xor pp (stepPar d rem hrem loc_i c0 (h ⟨rem, by omega⟩ - c0)))
          else 0) init) h' p =
        (l.foldl (fun (acc' : (Fin (rem + 2 ^ d * 2 ^ d) → ℕ) × Bool → ℕ) c0 =>
          fun hp => acc' hp + if hp.1 = stepHist d hd rem hrem h c0 then
            (h ⟨rem, by omega⟩).choose c0 * tab h (xor hp.2 (stepPar d rem hrem loc_i c0 (h ⟨rem, by omega⟩ - c0)))
          else 0) (fun hp => init hp.1 hp.2)) (h', p) := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons c0 t ih => intro init; exact ih _
    rw [hcurry, hstep]
    congr 1
    rw [← List.sum_toFinset _ List.nodup_range]
    have hrf : (List.range (h ⟨rem, by omega⟩ + 1)).toFinset = Finset.range (h ⟨rem, by omega⟩ + 1) := by
      ext x; simp
    rw [hrf]
    apply Finset.sum_congr rfl
    intro c0 _
    by_cases heq : h' = stepHist d hd rem hrem h c0
    · simp [heq]
    · have hne : stepHist d hd rem hrem h c0 ≠ h' := Ne.symm heq
      simp [heq, hne]
  have houter : ∀ (l : List (Fin (rem + 1 + 2 ^ d * 2 ^ d) → ℕ))
      (init : (Fin (rem + 2 ^ d * 2 ^ d) → ℕ) → Bool → ℕ),
      (l.foldl (fun acc h =>
        (List.range (h ⟨rem, by omega⟩ + 1)).foldl (fun acc' c0 =>
          fun hh pp => acc' hh pp + if hh = stepHist d hd rem hrem h c0 then
            (h ⟨rem, by omega⟩).choose c0 * tab h (xor pp (stepPar d rem hrem loc_i c0 (h ⟨rem, by omega⟩ - c0)))
          else 0) acc) init) h' p =
      init h' p + (l.map fun h => ∑ c0 ∈ Finset.range (h ⟨rem, by omega⟩ + 1),
        if stepHist d hd rem hrem h c0 = h' then
          (h ⟨rem, by omega⟩).choose c0 * tab h (xor p (stepPar d rem hrem loc_i c0 (h ⟨rem, by omega⟩ - c0)))
        else 0).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons h t ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, hinner]
      omega
  rw [houter, zero_add, ← List.sum_toFinset _ (nodup_allHists _ _)]

lemma dpInnerAux_spec {α : Type*} [DecidableEq α] (d : ℕ) (hd : 0 < d) (a0 : ℕ)
    (loc_i : Fin (2 ^ d) → Bool → Bool) (T : Finset α)
    (cur tgt : α → Fin a0 → Fin (2 ^ d)) :
    let D := 2 ^ d
    let countAt := fun (rem : ℕ) (H : Fin (rem + D * D) → ℕ) (par : Bool) =>
      ((T ×ˢ (Finset.univ : Finset (Fin a0 → Bool))).filter fun xb =>
        (∀ a : Fin a0, (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val < rem → xb.2 a = false) ∧
        (∀ j : Fin rem,
          (Finset.univ.filter fun a : Fin a0 => (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val = j.val).card =
            H ⟨j.val, by omega⟩) ∧
        (∀ j : Fin (D * D),
          (Finset.univ.filter fun a : Fin a0 =>
            rem ≤ (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val ∧
            pairIdx D (nextWin d hd (cur xb.1 a) (xb.2 a)) (tgt xb.1 a) = j).card =
            H ⟨rem + j.val, by omega⟩) ∧
        par = decide ((Finset.univ.filter fun a : Fin a0 =>
          rem ≤ (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val ∧
          loc_i (cur xb.1 a) (xb.2 a) = true).card % 2 = 1)).card
    ∀ (rem : ℕ) (hrem : rem ≤ D * D) (h' : Fin (D * D) → ℕ) (p : Bool),
      dpInnerAux d hd a0 loc_i rem hrem (countAt rem) h' p = countAt 0 (fun j => h' ⟨j.val, by omega⟩) p := by
  intro D countAt rem
  induction rem with
  | zero =>
    intro _ h' p
    rfl
  | succ rem ih =>
    intro hrem h' p
    dsimp only [dpInnerAux]
    have hstep : dpBinStep d hd a0 loc_i rem (by dsimp [D] at *; omega) (countAt (rem + 1)) = countAt rem := by
      funext H' par'
      rw [dpBinStep_eq_sum]

      let D2 := D * D
      let v0 : Fin D := ⟨rem / D, Nat.div_lt_of_lt_mul (by dsimp [D] at *; omega)⟩
      let w0 : Fin D := ⟨rem % D, Nat.mod_lt _ (by positivity)⟩
      have hpair0 : (pairIdx D v0 w0).val = rem := by
        dsimp only [pairIdx, v0, w0]
        have := Nat.div_add_mod rem D
        rw [Nat.mul_comm] at this; exact this
      let S_rem := fun x : α => Finset.univ.filter fun a : Fin a0 => (pairIdx D (cur x a) (tgt x a)).val = rem
      let hOf := fun (x : α) (b : Fin a0 → Bool) =>
        fun j : Fin (rem + 1 + D2) =>
          if hj : j.val < rem + 1 then
            (Finset.univ.filter fun a : Fin a0 => (pairIdx D (cur x a) (tgt x a)).val = j.val).card
          else
            (Finset.univ.filter fun a : Fin a0 =>
              rem + 1 ≤ (pairIdx D (cur x a) (tgt x a)).val ∧
              pairIdx D (nextWin d hd (cur x a) (b a)) (tgt x a) = ⟨j.val - (rem + 1), by dsimp [D2, D] at *; omega⟩).card
      let bZero := fun (x : α) (b : Fin a0 → Bool) =>
        fun a : Fin a0 => if (pairIdx D (cur x a) (tgt x a)).val = rem then false else b a

      have hhOf_sum : ∀ x b, ∑ j : Fin (rem + 1 + D2), hOf x b j = a0 := by
        intro x b
        have h1 : (∑ j : Fin (rem + 1 + D2), hOf x b j) =
            (∑ j : Fin (rem + 1), (Finset.univ.filter fun a : Fin a0 => (pairIdx D (cur x a) (tgt x a)).val = j.val).card) +
            (∑ j : Fin D2, (Finset.univ.filter fun a : Fin a0 =>
              rem + 1 ≤ (pairIdx D (cur x a) (tgt x a)).val ∧
              pairIdx D (nextWin d hd (cur x a) (b a)) (tgt x a) = j).card) := by
          rw [Fin.sum_univ_add]
          congr 1
          · apply Finset.sum_congr rfl; intro j _
            dsimp only [hOf, Fin.val_castAdd]
            rw [dite_eq_left_of_eq_true (eq_true j.isLt)]
          · apply Finset.sum_congr rfl; intro j _
            have hnot : ¬ (rem + 1 + j.val < rem + 1) := by omega
            simp only [hOf, Fin.val_natAdd, hnot, ↓reduceDIte]
            congr 1; ext a; simp
        rw [h1,
          ← Finset.card_biUnion (by
            intro j1 _ j2 _ hne
            simp only [Function.onFun, Finset.disjoint_left]; intro a ha1 ha2
            simp only [Finset.mem_filter] at ha1 ha2
            exact hne (Fin.ext (ha1.2.symm.trans ha2.2))),
          ← Finset.card_biUnion (by
            intro j1 _ j2 _ hne
            simp only [Function.onFun, Finset.disjoint_left]; intro a ha1 ha2
            simp only [Finset.mem_filter] at ha1 ha2
            exact hne (ha1.2.2.symm.trans ha2.2.2))]
        rw [← Finset.card_union_of_disjoint]
        · have huniv : ((Finset.univ : Finset (Fin (rem + 1))).biUnion (fun j => Finset.univ.filter fun a : Fin a0 => (pairIdx D (cur x a) (tgt x a)).val = j.val) ∪
              (Finset.univ : Finset (Fin D2)).biUnion (fun j => Finset.univ.filter fun a : Fin a0 => rem + 1 ≤ (pairIdx D (cur x a) (tgt x a)).val ∧ pairIdx D (nextWin d hd (cur x a) (b a)) (tgt x a) = j)) = Finset.univ := by
            ext a; simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and, iff_true]
            by_cases hlt : (pairIdx D (cur x a) (tgt x a)).val < rem + 1
            · exact Or.inl ⟨⟨_, hlt⟩, rfl⟩
            · exact Or.inr ⟨pairIdx D (nextWin d hd (cur x a) (b a)) (tgt x a), by omega, rfl⟩
          rw [huniv, Finset.card_univ, Fintype.card_fin]
        · rw [Finset.disjoint_left]
          intro a ha1 ha2
          simp only [Finset.mem_biUnion, Finset.mem_filter] at ha1 ha2
          rcases ha1 with ⟨j1, _, _, h1'⟩
          rcases ha2 with ⟨_, _, _, h2', _⟩
          omega

      have hchoose_bits : ∀ (S : Finset (Fin a0)) (c0 : ℕ),
          (Finset.univ.filter fun f : {a : Fin a0 // a ∈ S} → Bool =>
            (Finset.univ.filter fun a => f a = false).card = c0).card = S.card.choose c0 := by
        intro S c0
        rw [← Finset.card_powersetCard c0 S]
        refine Finset.card_bij (fun f _ => S.filter fun a => if ha : a ∈ S then f ⟨a, ha⟩ = false else false) ?_ ?_ ?_
        · intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
          rw [Finset.mem_powersetCard]
          refine ⟨Finset.filter_subset _ _, ?_⟩
          rw [← hf]
          refine Finset.card_bij (fun a _ => ⟨a, (Finset.mem_filter.mp (by assumption)).1⟩) ?_ ?_ ?_
          · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
            rw [dite_eq_left_of_eq_true (eq_true ha.1)] at ha; exact ha.2
          · intro a1 _ a2 _ heq; exact congrArg Subtype.val heq
          · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
            refine ⟨a.val, ?_, Subtype.ext rfl⟩
            simp [a.property, ha]
        · intro f1 _ f2 _ heq
          funext ⟨a, ha⟩
          have hmem : (a ∈ S.filter fun a => if ha : a ∈ S then f1 ⟨a, ha⟩ = false else false) ↔
              (a ∈ S.filter fun a => if ha : a ∈ S then f2 ⟨a, ha⟩ = false else false) := by rw [heq]
          simp only [Finset.mem_filter, ha, true_and, ↓reduceDIte] at hmem
          cases hf1 : f1 ⟨a, ha⟩ <;> cases hf2 : f2 ⟨a, ha⟩ <;> simp [hf1, hf2] at hmem ⊢
        · intro U hU
          rw [Finset.mem_powersetCard] at hU
          refine ⟨fun a => !decide (a.val ∈ U), ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [← hU.2]
            refine Finset.card_bij (fun a _ => a.val) ?_ ?_ ?_
            · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_false', decide_eq_true_eq] at ha; exact ha
            · intro a1 _ a2 _ heq; exact Subtype.ext heq
            · intro a ha; refine ⟨⟨a, hU.1 ha⟩, ?_, rfl⟩; simp [ha]
          · ext a; simp only [Finset.mem_filter]
            by_cases ha : a ∈ S
            · simp [ha]
            · simp [ha, show a ∉ U from fun h => ha (hU.1 h)]

      let Target := (T ×ˢ (Finset.univ : Finset (Fin a0 → Bool))).filter fun xb =>
        (∀ a : Fin a0, (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val < rem → xb.2 a = false) ∧
        (∀ j : Fin rem,
          (Finset.univ.filter fun a : Fin a0 => (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val = j.val).card =
            H' ⟨j.val, by dsimp [D] at *; omega⟩) ∧
        (∀ j : Fin D2,
          (Finset.univ.filter fun a : Fin a0 =>
            rem ≤ (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val ∧
            pairIdx D (nextWin d hd (cur xb.1 a) (xb.2 a)) (tgt xb.1 a) = j).card =
            H' ⟨rem + j.val, by dsimp [D2, D] at *; omega⟩) ∧
        par' = decide ((Finset.univ.filter fun a : Fin a0 =>
          rem ≤ (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val ∧
          loc_i (cur xb.1 a) (xb.2 a) = true).card % 2 = 1)
      show _ = Target.card

      have hpart : Target.card =
          ∑ h ∈ (allHists (rem + 1 + D2) a0).toFinset,
            ∑ c0 ∈ Finset.range (h ⟨rem, by dsimp [D2, D] at *; omega⟩ + 1),
              (Target.filter fun xb =>
                hOf xb.1 xb.2 = h ∧
                ((S_rem xb.1).filter fun a => xb.2 a = false).card = c0).card := by
        have hinner_part : ∀ h ∈ (allHists (rem + 1 + D2) a0).toFinset,
            (Target.filter fun xb => hOf xb.1 xb.2 = h).card =
              ∑ c0 ∈ Finset.range (h ⟨rem, by dsimp [D2, D] at *; omega⟩ + 1),
                (Target.filter fun xb =>
                  hOf xb.1 xb.2 = h ∧
                  ((S_rem xb.1).filter fun a => xb.2 a = false).card = c0).card := by
          intro h _
          rw [← Finset.card_biUnion (by
            intro c1 _ c2 _ hne
            simp only [Function.onFun, Finset.disjoint_left]; intro xb hx1 hx2
            simp only [Finset.mem_filter] at hx1 hx2
            exact hne (hx1.2.2.symm.trans hx2.2.2))]
          congr 1; ext xb
          simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
          constructor
          · rintro ⟨hxb, hh⟩
            refine ⟨((S_rem xb.1).filter fun a => xb.2 a = false).card, ?_, hxb, hh, rfl⟩
            have hle := Finset.card_filter_le (S_rem xb.1) (fun a => xb.2 a = false)
            have hrem_eq : hOf xb.1 xb.2 ⟨rem, by dsimp [D2, D] at *; omega⟩ = (S_rem xb.1).card := by simp [hOf, S_rem]
            rw [← hh, hrem_eq]; omega
          · rintro ⟨_, _, hxb, hh, _⟩; exact ⟨hxb, hh⟩
        calc Target.card
            = ((allHists (rem + 1 + D2) a0).toFinset.biUnion fun h => Target.filter fun xb => hOf xb.1 xb.2 = h).card := by
                congr 1; ext xb
                simp only [Finset.mem_biUnion, List.mem_toFinset, mem_allHists, Finset.mem_filter]
                constructor
                · intro hxb; exact ⟨hOf xb.1 xb.2, hhOf_sum xb.1 xb.2, hxb, rfl⟩
                · rintro ⟨_, _, hxb, _⟩; exact hxb
          _ = ∑ h ∈ (allHists (rem + 1 + D2) a0).toFinset, (Target.filter fun xb => hOf xb.1 xb.2 = h).card :=
                Finset.card_biUnion (by
                  intro h1 _ h2 _ hne
                  simp only [Function.onFun, Finset.disjoint_left]; intro xb hx1 hx2
                  simp only [Finset.mem_filter] at hx1 hx2
                  exact hne (hx1.2.symm.trans hx2.2))
          _ = _ := Finset.sum_congr rfl hinner_part
      rw [hpart]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro c0 hc0
      rw [Finset.mem_range] at hc0

      have hstep_prop : ∀ (x : α) (b : Fin a0 → Bool),
          hOf x b = h →
          ((S_rem x).filter fun a => b a = false).card = c0 →
          (∀ j : Fin rem,
            (Finset.univ.filter fun a : Fin a0 => (pairIdx D (cur x a) (tgt x a)).val = j.val).card =
              stepHist d hd rem (by dsimp [D] at hrem; omega) h c0 ⟨j.val, by dsimp [D] at hrem; omega⟩) ∧
          (∀ j : Fin D2,
            (Finset.univ.filter fun a : Fin a0 =>
              rem ≤ (pairIdx D (cur x a) (tgt x a)).val ∧
              pairIdx D (nextWin d hd (cur x a) (b a)) (tgt x a) = j).card =
              stepHist d hd rem (by dsimp [D] at hrem; omega) h c0 ⟨rem + j.val, by dsimp [D, D2] at hrem ⊢; omega⟩) ∧
          decide ((Finset.univ.filter fun a : Fin a0 =>
              rem ≤ (pairIdx D (cur x a) (tgt x a)).val ∧ loc_i (cur x a) (b a) = true).card % 2 = 1) =
            xor (decide ((Finset.univ.filter fun a : Fin a0 =>
              rem + 1 ≤ (pairIdx D (cur x a) (tgt x a)).val ∧ loc_i (cur x a) (bZero x b a) = true).card % 2 = 1))
              (stepPar d rem (by dsimp [D] at hrem; omega) loc_i c0 (h ⟨rem, by dsimp [D, D2] at hrem ⊢; omega⟩ - c0)) := by
        intro x b hhb hc0_eq
        have hScard : (S_rem x).card = h ⟨rem, by omega⟩ := by
          rw [← hhb]; simp [hOf, S_rem]
        have hS1 : ((S_rem x).filter fun a => b a = true).card = h ⟨rem, by omega⟩ - c0 := by
          have hsum := Finset.card_filter_add_card_filter_not (s := S_rem x) (p := fun a => b a = false)
          have hneg : ((S_rem x).filter fun a => ¬ (b a = false)) = ((S_rem x).filter fun a => b a = true) := by
            ext a; simp
          rw [hneg, hc0_eq, hScard] at hsum; omega
        have hin_rem : ∀ a ∈ S_rem x, cur x a = v0 ∧ tgt x a = w0 := by
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, S_rem] at ha
          exact pairIdx_injective D (cur x a) (tgt x a) v0 w0 (Fin.ext (ha.trans hpair0.symm))
        refine ⟨?_, ?_, ?_⟩
        · intro j
          have hjlt : j.val < rem := j.isLt
          have hne0 : j.val ≠ rem + (pairIdx (2 ^ d) (nextWin d hd ⟨rem / 2 ^ d, Nat.div_lt_of_lt_mul (by dsimp [D] at hrem; omega)⟩ false) ⟨rem % 2 ^ d, Nat.mod_lt _ (by positivity)⟩).val := by omega
          have hne1 : j.val ≠ rem + (pairIdx (2 ^ d) (nextWin d hd ⟨rem / 2 ^ d, Nat.div_lt_of_lt_mul (by dsimp [D] at hrem; omega)⟩ true) ⟨rem % 2 ^ d, Nat.mod_lt _ (by positivity)⟩).val := by omega
          dsimp only [stepHist]
          rw [dite_eq_left_of_eq_true (eq_true hjlt), if_neg hne0, if_neg hne1, add_zero, add_zero]
          rw [← hhb]; simp [hOf]
        · intro j
          have hsplit : (Finset.univ.filter fun a : Fin a0 =>
              rem ≤ (pairIdx D (cur x a) (tgt x a)).val ∧
              pairIdx D (nextWin d hd (cur x a) (b a)) (tgt x a) = j).card =
            (Finset.univ.filter fun a : Fin a0 =>
              rem + 1 ≤ (pairIdx D (cur x a) (tgt x a)).val ∧
              pairIdx D (nextWin d hd (cur x a) (b a)) (tgt x a) = j).card +
            ((S_rem x).filter fun a => b a = false ∧ pairIdx D (nextWin d hd v0 false) w0 = j).card +
            ((S_rem x).filter fun a => b a = true ∧ pairIdx D (nextWin d hd v0 true) w0 = j).card := by
            rw [← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
            · congr 1; ext a
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, S_rem]
              constructor
              · rintro ⟨hge, hp⟩
                by_cases heq : (pairIdx D (cur x a) (tgt x a)).val = rem
                · have ⟨hv, hw⟩ := hin_rem a (by simp [S_rem, heq])
                  rw [hv, hw] at hp
                  cases hb : b a
                  · rw [hb] at hp; exact Or.inl (Or.inr ⟨heq, rfl, hp⟩)
                  · rw [hb] at hp; exact Or.inr ⟨heq, rfl, hp⟩
                · exact Or.inl (Or.inl ⟨by omega, hp⟩)
              · rintro ((⟨hge, hp⟩ | ⟨heq, hb, hp⟩) | ⟨heq, hb, hp⟩)
                · exact ⟨by omega, hp⟩
                · have ⟨hv, hw⟩ := hin_rem a (by simp [S_rem, heq])
                  exact ⟨by omega, by rw [hv, hw, hb]; exact hp⟩
                · have ⟨hv, hw⟩ := hin_rem a (by simp [S_rem, heq])
                  exact ⟨by omega, by rw [hv, hw, hb]; exact hp⟩
            · rw [Finset.disjoint_left]; intro a ha1 ha2
              simp only [Finset.mem_union, Finset.mem_filter, S_rem] at ha1 ha2
              rcases ha1 with ha1 | ha1
              · omega
              · rw [ha1.2.1] at ha2; exact Bool.false_ne_true ha2.2.1
            · rw [Finset.disjoint_left]; intro a ha1 ha2
              simp only [Finset.mem_filter, S_rem] at ha1 ha2; omega
          rw [hsplit]
          have h1 : (Finset.univ.filter fun a : Fin a0 =>
              rem + 1 ≤ (pairIdx D (cur x a) (tgt x a)).val ∧
              pairIdx D (nextWin d hd (cur x a) (b a)) (tgt x a) = j).card = h ⟨rem + j.val + 1, by dsimp [D, D2] at *; omega⟩ := by
            rw [← hhb]
            have hnot : ¬ (rem + j.val + 1 < rem + 1) := by omega
            simp only [hOf, hnot, ↓reduceDIte]
            congr 1; ext a; simp [show rem + j.val + 1 - (rem + 1) = j.val by omega]
          have h2 : ((S_rem x).filter fun a => b a = false ∧ pairIdx D (nextWin d hd v0 false) w0 = j).card =
              if rem + j.val = rem + (pairIdx D (nextWin d hd v0 false) w0).val then c0 else 0 := by
            by_cases hj : pairIdx D (nextWin d hd v0 false) w0 = j
            · subst hj; simp [hc0_eq]
            · have hne : rem + j.val ≠ rem + (pairIdx D (nextWin d hd v0 false) w0).val := by
                intro heq; exact hj (Fin.ext (by omega))
              rw [if_neg hne]; simp [hj]
          have h3 : ((S_rem x).filter fun a => b a = true ∧ pairIdx D (nextWin d hd v0 true) w0 = j).card =
              if rem + j.val = rem + (pairIdx D (nextWin d hd v0 true) w0).val then h ⟨rem, by omega⟩ - c0 else 0 := by
            by_cases hj : pairIdx D (nextWin d hd v0 true) w0 = j
            · subst hj; simp [hS1]
            · have hne : rem + j.val ≠ rem + (pairIdx D (nextWin d hd v0 true) w0).val := by
                intro heq; exact hj (Fin.ext (by omega))
              rw [if_neg hne]; simp [hj]
          rw [h1, h2, h3]
          dsimp only [stepHist]
          have hnot : ¬ (rem + j.val < rem) := by omega
          simp only [hnot, ↓reduceDIte]
          rfl
        · have hpsplit : (Finset.univ.filter fun a : Fin a0 =>
              rem ≤ (pairIdx D (cur x a) (tgt x a)).val ∧ loc_i (cur x a) (b a) = true).card =
            (Finset.univ.filter fun a : Fin a0 =>
              rem + 1 ≤ (pairIdx D (cur x a) (tgt x a)).val ∧ loc_i (cur x a) (bZero x b a) = true).card +
            (if loc_i v0 false = true then c0 else 0) +
            (if loc_i v0 true = true then h ⟨rem, by omega⟩ - c0 else 0) := by
            have hrem_ge : (Finset.univ.filter fun a : Fin a0 =>
                rem + 1 ≤ (pairIdx D (cur x a) (tgt x a)).val ∧ loc_i (cur x a) (bZero x b a) = true) =
              (Finset.univ.filter fun a : Fin a0 =>
                rem + 1 ≤ (pairIdx D (cur x a) (tgt x a)).val ∧ loc_i (cur x a) (b a) = true) := by
              ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, bZero]
              constructor <;> rintro ⟨hge, hl⟩ <;> exact ⟨hge, by simp [show (pairIdx D (cur x a) (tgt x a)).val ≠ rem by omega] at hl ⊢; exact hl⟩
            rw [hrem_ge]
            have h0 : ((S_rem x).filter fun a => b a = false ∧ loc_i v0 false = true).card =
                if loc_i v0 false = true then c0 else 0 := by
              cases hl : loc_i v0 false <;> simp [hl, hc0_eq]
            have h1 : ((S_rem x).filter fun a => b a = true ∧ loc_i v0 true = true).card =
                if loc_i v0 true = true then h ⟨rem, by omega⟩ - c0 else 0 := by
              cases hl : loc_i v0 true <;> simp [hl, hS1]
            rw [← h0, ← h1, ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
            · congr 1; ext a
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, S_rem]
              constructor
              · rintro ⟨hge, hl⟩
                by_cases heq : (pairIdx D (cur x a) (tgt x a)).val = rem
                · have ⟨hv, _⟩ := hin_rem a (by simp [S_rem, heq])
                  rw [hv] at hl
                  cases hb : b a
                  · rw [hb] at hl; exact Or.inl (Or.inr ⟨heq, rfl, hl⟩)
                  · rw [hb] at hl; exact Or.inr ⟨heq, rfl, hl⟩
                · exact Or.inl (Or.inl ⟨by omega, hl⟩)
              · rintro ((⟨hge, hl⟩ | ⟨heq, hb, hl⟩) | ⟨heq, hb, hl⟩)
                · exact ⟨by omega, hl⟩
                · have ⟨hv, _⟩ := hin_rem a (by simp [S_rem, heq])
                  exact ⟨by omega, by rw [hv, hb]; exact hl⟩
                · have ⟨hv, _⟩ := hin_rem a (by simp [S_rem, heq])
                  exact ⟨by omega, by rw [hv, hb]; exact hl⟩
            · rw [Finset.disjoint_left]; intro a ha1 ha2
              simp only [Finset.mem_union, Finset.mem_filter, S_rem] at ha1 ha2
              rcases ha1 with ha1 | ha1
              · omega
              · rw [ha1.2.1] at ha2; exact Bool.false_ne_true ha2.2.1
            · rw [Finset.disjoint_left]; intro a ha1 ha2
              simp only [Finset.mem_filter, S_rem] at ha1 ha2; omega
          rw [hpsplit]
          dsimp only [stepPar]
          set A := (Finset.univ.filter fun a : Fin a0 =>
            rem + 1 ≤ (pairIdx D (cur x a) (tgt x a)).val ∧ loc_i (cur x a) (bZero x b a) = true).card
          cases loc_i v0 false <;> cases loc_i v0 true <;>
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.and_true, add_zero] <;>
            rcases Nat.mod_two_eq_zero_or_one A with hA | hA <;>
            rcases Nat.mod_two_eq_zero_or_one c0 with hc0m | hc0m <;>
            rcases Nat.mod_two_eq_zero_or_one (h ⟨rem, by omega⟩ - c0) with hc1m | hc1m <;>
            simp [Nat.add_mod, hA, hc0m, hc1m]

      by_cases hH : stepHist d hd rem (by dsimp [D] at hrem; omega) h c0 = H'
      · rw [if_pos hH]

        let pf := stepPar d rem (by dsimp [D] at hrem; omega) loc_i c0 (h ⟨rem, by dsimp [D, D2] at hrem ⊢; omega⟩ - c0)
        let OldSet := (T ×ˢ (Finset.univ : Finset (Fin a0 → Bool))).filter fun xb =>
          (∀ a : Fin a0, (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val < rem + 1 → xb.2 a = false) ∧
          (∀ j : Fin (rem + 1),
            (Finset.univ.filter fun a : Fin a0 => (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val = j.val).card =
              h ⟨j.val, by dsimp [D, D2] at hrem ⊢; omega⟩) ∧
          (∀ j : Fin D2,
            (Finset.univ.filter fun a : Fin a0 =>
              rem + 1 ≤ (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val ∧
              pairIdx D (nextWin d hd (cur xb.1 a) (xb.2 a)) (tgt xb.1 a) = j).card =
              h ⟨rem + 1 + j.val, by dsimp [D, D2] at hrem ⊢; omega⟩) ∧
          xor par' pf = decide ((Finset.univ.filter fun a : Fin a0 =>
            rem + 1 ≤ (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val ∧
            loc_i (cur xb.1 a) (xb.2 a) = true).card % 2 = 1)
        show (h ⟨rem, by dsimp [D, D2] at hrem ⊢; omega⟩).choose c0 * OldSet.card = _
        symm
        rw [Nat.mul_comm, ← smul_eq_mul, ← Finset.sum_const]
        have hfib : (Target.filter fun xb =>
            hOf xb.1 xb.2 = h ∧ ((S_rem xb.1).filter fun a => xb.2 a = false).card = c0).card =
            ∑ xb_old ∈ OldSet, ((Target.filter fun xb =>
              hOf xb.1 xb.2 = h ∧ ((S_rem xb.1).filter fun a => xb.2 a = false).card = c0).filter
              fun xb => (xb.1, bZero xb.1 xb.2) = xb_old).card := by
          rw [← Finset.card_biUnion]
          · congr 1; ext xb
            simp only [Finset.mem_biUnion, Finset.mem_filter]
            constructor
            · rintro ⟨hxb, hh', hc0'⟩
              refine ⟨(xb.1, bZero xb.1 xb.2), ?_, ⟨hxb, hh', hc0'⟩, rfl⟩
              simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, OldSet]
              simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, Target] at hxb
              have hsp := hstep_prop xb.1 xb.2 hh' hc0'
              refine ⟨hxb.1, ?_, ?_, ?_, ?_⟩
              · intro a ha
                dsimp only [bZero]
                by_cases heq : (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val = rem
                · simp [heq]
                · simp [heq]; exact hxb.2.1 a (by omega)
              · intro j
                have hjj := congrFun hh' ⟨j.val, by dsimp [D, D2] at hrem ⊢; omega⟩
                dsimp only [hOf] at hjj
                rw [dite_eq_left_of_eq_true (eq_true j.isLt)] at hjj
                exact hjj
              · intro j
                have := congrFun hh' ⟨rem + 1 + j.val, by dsimp [D, D2] at hrem ⊢; omega⟩
                have hnot : ¬ (rem + 1 + j.val < rem + 1) := by omega
                simp only [hOf, hnot, ↓reduceDIte, Nat.add_sub_cancel_left] at this
                rw [← this]
                congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, bZero]
                constructor <;> rintro ⟨hge, hp⟩ <;> exact ⟨hge, by simp [show (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val ≠ rem by omega] at hp ⊢; exact hp⟩
              · have hp' := hxb.2.2.2.2
                rw [hsp.2.2] at hp'
                rw [hp']; dsimp only [pf]
                cases decide ((Finset.univ.filter fun a : Fin a0 =>
                  rem + 1 ≤ (pairIdx D (cur xb.1 a) (tgt xb.1 a)).val ∧ loc_i (cur xb.1 a) (bZero xb.1 xb.2 a) = true).card % 2 = 1) <;>
                  cases stepPar d rem (by dsimp [D] at hrem; omega) loc_i c0 (h ⟨rem, by dsimp [D, D2] at hrem ⊢; omega⟩ - c0) <;> rfl
            · rintro ⟨_, _, hmem, _⟩; exact hmem
          · intro x1 _ x2 _ hne
            simp only [Function.onFun, Finset.disjoint_left]; intro xb hx1 hx2
            simp only [Finset.mem_filter] at hx1 hx2
            exact hne (hx1.2.symm.trans hx2.2)
        rw [hfib]
        apply Finset.sum_congr rfl
        intro xb_old hold
        simp only [OldSet, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true] at hold
        have hScard : (S_rem xb_old.1).card = h ⟨rem, by dsimp [D, D2] at hrem ⊢; omega⟩ := by
          simpa [S_rem] using hold.2.2.1 ⟨rem, by omega⟩
        rw [← hScard, ← hchoose_bits (S_rem xb_old.1) c0]
        refine Finset.card_bij (fun xb _ => fun a : {a : Fin a0 // a ∈ S_rem xb_old.1} => xb.2 a.val) ?_ ?_ ?_
        · intro xb hxb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxb ⊢
          rcases hxb with ⟨⟨_, _, hc0'⟩, hproj⟩
          have hx1 : xb.1 = xb_old.1 := by rw [← hproj]
          rw [hx1] at hc0'
          rw [← hc0']
          refine Finset.card_bij (fun a _ => a.val) ?_ ?_ ?_
          · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
            exact ⟨a.property, ha⟩
          · intro a1 _ a2 _ heq; exact Subtype.ext heq
          · intro a ha; simp only [Finset.mem_filter] at ha
            exact ⟨⟨a, ha.1⟩, by simp [ha.2], rfl⟩
        · intro xb1 hxb1 xb2 hxb2 heq
          simp only [Finset.mem_filter] at hxb1 hxb2
          have hx1 : xb1.1 = xb_old.1 := by rw [← hxb1.2]
          have hx2 : xb2.1 = xb_old.1 := by rw [← hxb2.2]
          have hb1 : bZero xb1.1 xb1.2 = xb_old.2 := by rw [← hxb1.2]
          have hb2 : bZero xb2.1 xb2.2 = xb_old.2 := by rw [← hxb2.2]
          apply Prod.ext (hx1.trans hx2.symm)
          funext a
          by_cases ha : a ∈ S_rem xb_old.1
          · exact congrFun heq ⟨a, ha⟩
          · have hne1 : (pairIdx D (cur xb1.1 a) (tgt xb1.1 a)).val ≠ rem := by
              rw [hx1]; simpa [S_rem] using ha
            have hne2 : (pairIdx D (cur xb2.1 a) (tgt xb2.1 a)).val ≠ rem := by
              rw [hx2]; simpa [S_rem] using ha
            have h1 := congrFun hb1 a
            have h2 := congrFun hb2 a
            simp only [bZero, hne1, hne2, ↓reduceIte] at h1 h2
            exact h1.trans h2.symm
        · intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
          let b_new : Fin a0 → Bool := fun a =>
            if ha : a ∈ S_rem xb_old.1 then f ⟨a, ha⟩ else xb_old.2 a
          refine ⟨(xb_old.1, b_new), ?_, ?_⟩
          · have hbzero : bZero xb_old.1 b_new = xb_old.2 := by
              funext a
              dsimp only [bZero, b_new]
              by_cases ha : (pairIdx D (cur xb_old.1 a) (tgt xb_old.1 a)).val = rem
              · simp [ha, hold.2.1 a (by omega)]
              · have hnot : a ∉ S_rem xb_old.1 := by simp [S_rem, ha]
                simp [ha, hnot]
            have hhof : hOf xb_old.1 b_new = h := by
              funext j
              dsimp only [hOf]
              by_cases hj : j.val < rem + 1
              · simp only [hj, ↓reduceDIte]
                exact hold.2.2.1 ⟨j.val, hj⟩
              · simp only [hj, ↓reduceDIte]
                have h2 := hold.2.2.2.1 ⟨j.val - (rem + 1), by omega⟩
                have hidx : rem + 1 + (j.val - (rem + 1)) = j.val := by omega
                rw [show (⟨rem + 1 + (j.val - (rem + 1)), _⟩ : Fin (rem + 1 + D2)) = j from Fin.ext hidx] at h2
                rw [← h2]
                congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, b_new]
                constructor <;> rintro ⟨hge, hp⟩ <;>
                  exact ⟨hge, by have hnot : a ∉ S_rem xb_old.1 := by simp [S_rem]; omega
                                 simp [hnot] at hp ⊢; exact hp⟩
            have hc0_new : ((S_rem xb_old.1).filter fun a => b_new a = false).card = c0 := by
              rw [← hf]
              refine Finset.card_bij (fun a _ => ⟨a, (Finset.mem_filter.mp (by assumption)).1⟩) ?_ ?_ ?_
              · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and, b_new] at ha ⊢
                rw [dite_eq_left_of_eq_true (eq_true ha.1)] at ha; exact ha.2
              · intro a1 _ a2 _ heq; exact congrArg Subtype.val heq
              · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
                refine ⟨a.val, ?_, Subtype.ext rfl⟩
                simp [b_new, a.property, ha]
            have hsp := hstep_prop xb_old.1 b_new hhof hc0_new
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, Target]
            refine ⟨⟨⟨hold.1, ?_, ?_, ?_, ?_⟩, hhof, hc0_new⟩, Prod.ext rfl hbzero⟩
            · intro a ha
              have hnot : a ∉ S_rem xb_old.1 := by simp [S_rem]; omega
              simp [b_new, hnot, hold.2.1 a (by omega)]
            · intro j; rw [hsp.1 j, hH]
            · intro j; rw [hsp.2.1 j, hH]
            · rw [hsp.2.2, hbzero, ← hold.2.2.2.2]
              dsimp only [pf]
              cases par' <;> cases stepPar d rem (by dsimp [D] at hrem; omega) loc_i c0 (h ⟨rem, by dsimp [D, D2] at hrem ⊢; omega⟩ - c0) <;> rfl
          · funext ⟨a, ha⟩
            simp [b_new, ha]
      · rw [if_neg hH]
        symm
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro xb hxb ⟨hh', hc0'⟩
        simp only [Finset.mem_filter, Target] at hxb
        have hsp := hstep_prop xb.1 xb.2 hh' hc0'
        apply hH
        funext j
        by_cases hj : j.val < rem
        · have h1 := hsp.1 ⟨j.val, hj⟩
          have h2 := hxb.2.2.1 ⟨j.val, hj⟩
          exact h1.symm.trans h2
        · have h1 := hsp.2.1 ⟨j.val - rem, by dsimp [D, D2] at hrem ⊢; omega⟩
          have h2 := hxb.2.2.2.1 ⟨j.val - rem, by dsimp [D, D2] at hrem ⊢; omega⟩
          have heq : (⟨rem + (j.val - rem), by dsimp [D, D2] at hrem ⊢; omega⟩ : Fin (rem + D2)) = j := Fin.ext (by dsimp; omega)
          rw [heq] at h1 h2
          exact h1.symm.trans h2
    rw [hstep]
    exact ih (by omega) h' p

def bitsToFin (k : ℕ) (f : ℕ → Bool) : Fin (2 ^ k) :=
  ⟨∑ i : Fin k, if f i.val then 2 ^ i.val else 0, by
    have hsum : ∀ (m : ℕ) (g : Fin m → Bool), (∑ i : Fin m, if g i then 2 ^ i.val else 0) < 2 ^ m := by
      intro m; induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro g; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
        have := ih (fun i => g i.castSucc); have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
        split_ifs <;> omega
    exact hsum k (fun i => f i.val)⟩

lemma bitsToFin_testBit (k : ℕ) (f : ℕ → Bool) (i : ℕ) (hi : i < k) :
    (bitsToFin k f).val.testBit i = f i := by
  dsimp only [bitsToFin]
  have hgen : ∀ (m : ℕ) (g : Fin m → Bool) (j : ℕ) (hj : j < m),
      (∑ t : Fin m, if g t then 2 ^ t.val else 0).testBit j = g ⟨j, hj⟩ := by
    intro m; induction m with
    | zero => intro _ _ hj; omega
    | succ m ih =>
      intro g j hj
      rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
      set lo := ∑ t : Fin m, if g t.castSucc = true then 2 ^ t.val else 0
      have hlo : lo < 2 ^ m := by
        have hsum : ∀ (m' : ℕ) (h : Fin m' → Bool), (∑ t : Fin m', if h t then 2 ^ t.val else 0) < 2 ^ m' := by
          intro m'; induction m' with
          | zero => intro _; simp
          | succ m' ih' =>
            intro h; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
            have := ih' (fun t => h t.castSucc); have : 2 ^ (m' + 1) = 2 ^ m' + 2 ^ m' := by rw [pow_succ]; omega
            split_ifs <;> omega
        exact hsum m _
      by_cases hjm : j = m
      · subst hjm
        cases hg : g (Fin.last j)
        · simp [Nat.testBit_lt_two_pow hlo]; exact hg
        · simp only [↓reduceIte]
          rw [Nat.add_comm lo, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlo]; exact hg.symm
      · have hjlt : j < m := by omega
        cases hg : g (Fin.last m)
        · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
          exact ih (fun t => g t.castSucc) j hjlt
        · simp only [↓reduceIte]
          rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hjlt]
          exact ih (fun t => g t.castSucc) j hjlt
  exact hgen k (fun t => f t.val) i hi

def unrankLoop (k : ℕ) (cntPref : ℕ → (ℕ → Bool) → ℕ) :
    ℕ → ℕ × (ℕ → Bool) → ℕ × (ℕ → Bool)
  | 0, st => st
  | m + 1, (rem, pref) =>
    let pref0 := Function.update pref m false
    let c0 := cntPref m pref0
    if rem < c0 then
      unrankLoop k cntPref m (rem, pref0)
    else
      unrankLoop k cntPref m (rem - c0, Function.update pref m true)

lemma lt_of_prefMatch_bit_false_true (k m : ℕ) (hm : m < k) (pref : ℕ → Bool)
    (z w : Fin (2 ^ k))
    (hz : prefMatch k m (Function.update pref m false) z)
    (hw : prefMatch k m (Function.update pref m true) w) :
    z < w := by

  have hhi : z.val / 2 ^ (m + 1) = w.val / 2 ^ (m + 1) := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    by_cases hlt : m + 1 + j < k
    · have hz' := hz (m + 1 + j) (by omega) hlt
      have hw' := hw (m + 1 + j) (by omega) hlt
      have hne : m + 1 + j ≠ m := by omega
      simp only [Function.update_of_ne hne] at hz' hw'
      rw [Nat.add_comm j (m + 1), hz', hw']
    · have hge : k ≤ j + (m + 1) := by omega
      have h1 : z.val < 2 ^ (j + (m + 1)) := lt_of_lt_of_le z.isLt (Nat.pow_le_pow_right (by omega) hge)
      have h2 : w.val < 2 ^ (j + (m + 1)) := lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by omega) hge)
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
  have hzm : z.val.testBit m = false := by
    have := hz m le_rfl hm; simp only [Function.update_self] at this; exact this
  have hwm : w.val.testBit m = true := by
    have := hw m le_rfl hm; simp only [Function.update_self] at this; exact this
  have hdiv_z : z.val % 2 ^ (m + 1) < 2 ^ m := by
    have h1 := Nat.mod_lt z.val (show 0 < 2 ^ (m + 1) by positivity)
    have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
    by_contra hge
    have hge' : 2 ^ m ≤ z.val % 2 ^ (m + 1) := by omega
    have hsub : z.val % 2 ^ (m + 1) = 2 ^ m + (z.val % 2 ^ (m + 1) - 2 ^ m) := by omega
    have htb : (z.val % 2 ^ (m + 1)).testBit m = true := by
      rw [hsub, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)]; rfl
    rw [Nat.testBit_mod_two_pow] at htb
    simp only [lt_add_iff_pos_right, zero_lt_one, decide_true, Bool.true_and, hzm] at htb
    exact Bool.false_ne_true htb
  have hdiv_w : 2 ^ m ≤ w.val % 2 ^ (m + 1) := by
    by_contra hlt
    have htb : (w.val % 2 ^ (m + 1)).testBit m = false := Nat.testBit_lt_two_pow (by omega)
    rw [Nat.testBit_mod_two_pow] at htb
    simp only [lt_add_iff_pos_right, zero_lt_one, decide_true, Bool.true_and, hwm] at htb
    exact Bool.false_ne_true htb.symm
  have hdz := Nat.div_add_mod z.val (2 ^ (m + 1))
  have hdw := Nat.div_add_mod w.val (2 ^ (m + 1))
  rw [hhi] at hdz
  exact Fin.mk_lt_mk.mpr (by omega)

open Classical in
lemma unrankLoop_spec (k : ℕ) (P : Fin (2 ^ k) → Prop) [DecidablePred P]
    (cntPref : ℕ → (ℕ → Bool) → ℕ)
    (hcnt : ∀ m < k, ∀ pref, cntPref m pref = (Finset.univ.filter fun w : Fin (2 ^ k) => prefMatch k m pref w ∧ P w).card) :
    ∀ (m : ℕ) (hm : m ≤ k) (rem : ℕ) (pref : ℕ → Bool),
      rem < (Finset.univ.filter fun w : Fin (2 ^ k) => prefMatch k m pref w ∧ P w).card →
      let res := unrankLoop k cntPref m (rem, pref)
      let w := bitsToFin k res.2
      prefMatch k m pref w ∧ P w ∧
      (Finset.univ.filter fun z : Fin (2 ^ k) => z < w ∧ prefMatch k m pref z ∧ P z).card = rem := by
  intro m
  induction m with
  | zero =>
    intro _ rem pref hrem
    dsimp only [unrankLoop]
    set w := bitsToFin k pref
    have huniq : Finset.univ.filter (fun z : Fin (2 ^ k) => prefMatch k 0 pref z ∧ P z) ⊆ {w} := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hz ⊢
      apply Fin.ext; apply Nat.eq_of_testBit_eq; intro pos
      by_cases hpos : pos < k
      · rw [hz.1 pos (Nat.zero_le _) hpos, bitsToFin_testBit k pref pos hpos]
      · have h1 : z.val < 2 ^ pos := lt_of_lt_of_le z.isLt (Nat.pow_le_pow_right (by omega) (by omega))
        have h2 : w.val < 2 ^ pos := lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by omega) (by omega))
        rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    have hcard_le : (Finset.univ.filter fun z : Fin (2 ^ k) => prefMatch k 0 pref z ∧ P z).card ≤ 1 :=
      le_trans (Finset.card_le_card huniq) (by simp)
    have hrem0 : rem = 0 := by omega
    have hne : (Finset.univ.filter fun z : Fin (2 ^ k) => prefMatch k 0 pref z ∧ P z).Nonempty :=
      Finset.card_pos.mp (by omega)
    rcases hne with ⟨z, hz⟩
    have hzw : z = w := Finset.mem_singleton.mp (huniq hz)
    subst hzw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine ⟨hz.1, hz.2, ?_⟩
    rw [hrem0, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z' _ ⟨hlt, hp, hPz⟩
    have : z' = w := Finset.mem_singleton.mp (huniq (by simp [hp, hPz]))
    exact lt_irrefl w (this ▸ hlt)
  | succ m ih =>
    intro hm rem pref hrem
    dsimp only [unrankLoop]
    set pref0 := Function.update pref m false
    set pref1 := Function.update pref m true
    have hc0_eq : cntPref m pref0 = (Finset.univ.filter fun w : Fin (2 ^ k) => prefMatch k m pref0 w ∧ P w).card :=
      hcnt m (by omega) pref0
    have hsplit : (Finset.univ.filter fun w : Fin (2 ^ k) => prefMatch k (m + 1) pref w ∧ P w).card =
        (Finset.univ.filter fun w : Fin (2 ^ k) => prefMatch k m pref0 w ∧ P w).card +
        (Finset.univ.filter fun w : Fin (2 ^ k) => prefMatch k m pref1 w ∧ P w).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext w
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hpm, hPw⟩
          cases hbm : w.val.testBit m
          · left; refine ⟨fun pos hlo hhi => ?_, hPw⟩
            by_cases heq : pos = m
            · subst heq; simp [pref0, hbm]
            · simp [pref0, Function.update_of_ne heq, hpm pos (by omega) hhi]
          · right; refine ⟨fun pos hlo hhi => ?_, hPw⟩
            by_cases heq : pos = m
            · subst heq; simp [pref1, hbm]
            · simp [pref1, Function.update_of_ne heq, hpm pos (by omega) hhi]
        · rintro (⟨hpm, hPw⟩ | ⟨hpm, hPw⟩)
          · refine ⟨fun pos hlo hhi => ?_, hPw⟩
            have hne : pos ≠ m := by omega
            have := hpm pos (by omega) hhi; simpa [pref0, Function.update_of_ne hne] using this
          · refine ⟨fun pos hlo hhi => ?_, hPw⟩
            have hne : pos ≠ m := by omega
            have := hpm pos (by omega) hhi; simpa [pref1, Function.update_of_ne hne] using this
      · rw [Finset.disjoint_left]; intro w hw0 hw1
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw0 hw1
        have h0 := hw0.1 m le_rfl (by omega); simp [pref0] at h0
        have h1 := hw1.1 m le_rfl (by omega); simp [pref1] at h1
        rw [h0] at h1; exact Bool.false_ne_true h1
    split_ifs with hlt
    · have hrec := ih (by omega) rem pref0 (by omega)
      dsimp only [pref0] at hrec ⊢
      refine ⟨fun pos hlo hhi => ?_, hrec.2.1, ?_⟩
      · have hne : pos ≠ m := by omega
        have := hrec.1 pos (by omega) hhi; simpa [Function.update_of_ne hne] using this
      · refine Eq.trans ?_ hrec.2.2
        congr 1; ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hzlt, hpm, hPz⟩
          refine ⟨hzlt, fun pos hlo hhi => ?_, hPz⟩
          by_cases heq : pos = m
          · subst heq
            simp only [Function.update_self]
            by_contra hne
            have hzt : z.val.testBit pos = true := by cases h : z.val.testBit pos <;> simp [h] at hne ⊢
            have hzp1 : prefMatch k pos (Function.update pref pos true) z := fun p' hlo' hhi' => by
              by_cases hp' : p' = pos
              · subst hp'; simp [hzt]
              · simp [Function.update_of_ne hp', hpm p' (by omega) hhi']
            have hgt := lt_of_prefMatch_bit_false_true k pos (by omega) pref _ z hrec.1 hzp1
            exact lt_asymm hzlt hgt
          · simp [Function.update_of_ne heq, hpm pos (by omega) hhi]
        · rintro ⟨hzlt, hpm, hPz⟩
          refine ⟨hzlt, fun pos hlo hhi => ?_, hPz⟩
          have hne : pos ≠ m := by omega
          have := hpm pos (by omega) hhi; simpa [Function.update_of_ne hne] using this
    · have hrec := ih (by omega) (rem - cntPref m pref0) pref1 (by omega)
      refine ⟨fun pos hlo hhi => ?_, hrec.2.1, ?_⟩
      · have hne : pos ≠ m := by omega
        have := hrec.1 pos (by omega) hhi; simpa [pref1, Function.update_of_ne hne] using this
      · have hpart_lt : (Finset.univ.filter fun z : Fin (2 ^ k) =>
            z < bitsToFin k (unrankLoop k cntPref m (rem - cntPref m pref0, pref1)).2 ∧
            prefMatch k (m + 1) pref z ∧ P z).card =
          (Finset.univ.filter fun z : Fin (2 ^ k) => prefMatch k m pref0 z ∧ P z).card +
          (Finset.univ.filter fun z : Fin (2 ^ k) =>
            z < bitsToFin k (unrankLoop k cntPref m (rem - cntPref m pref0, pref1)).2 ∧
            prefMatch k m pref1 z ∧ P z).card := by
          rw [← Finset.card_union_of_disjoint]
          · congr 1; ext z
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hzlt, hpm, hPz⟩
              cases hzm : z.val.testBit m
              · left; refine ⟨fun pos hlo hhi => ?_, hPz⟩
                by_cases heq : pos = m
                · subst heq; simp [pref0, hzm]
                · simp [pref0, Function.update_of_ne heq, hpm pos (by omega) hhi]
              · right; refine ⟨hzlt, fun pos hlo hhi => ?_, hPz⟩
                by_cases heq : pos = m
                · subst heq; simp [pref1, hzm]
                · simp [pref1, Function.update_of_ne heq, hpm pos (by omega) hhi]
            · rintro (⟨hpm0, hPz⟩ | ⟨hzlt, hpm1, hPz⟩)
              · refine ⟨lt_of_prefMatch_bit_false_true k m (by omega) pref z _ hpm0 hrec.1, fun pos hlo hhi => ?_, hPz⟩
                have hne : pos ≠ m := by omega
                have := hpm0 pos (by omega) hhi; simpa [pref0, Function.update_of_ne hne] using this
              · refine ⟨hzlt, fun pos hlo hhi => ?_, hPz⟩
                have hne : pos ≠ m := by omega
                have := hpm1 pos (by omega) hhi; simpa [pref1, Function.update_of_ne hne] using this
          · rw [Finset.disjoint_left]; intro z hz0 hz1
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz0 hz1
            have h0 := hz0.1 m le_rfl (by omega); simp [pref0] at h0
            have h1 := hz1.2.1 m le_rfl (by omega); simp [pref1] at h1
            rw [h0] at h1; exact Bool.false_ne_true h1
        rw [hpart_lt, hrec.2.2, ← hc0_eq]; omega

def evolvePref (d : ℕ) (hd : 0 < d) (v : Fin (2 ^ d)) {i : ℕ} (bits : Fin i → Bool) :
    (j : ℕ) → j ≤ i → Fin (2 ^ d)
  | 0, _ => v
  | j + 1, hj => nextWin d hd (evolvePref d hd v bits j (by omega)) (bits ⟨j, hj⟩)

lemma evolvePref_snoc (d : ℕ) (hd : 0 < d) (v : Fin (2 ^ d)) {i : ℕ} (bits : Fin i → Bool) (b : Bool)
    (j : ℕ) (hj : j ≤ i) :
    evolvePref d hd v (Fin.snoc (α := fun _ => Bool) bits b) j (by omega) =
      evolvePref d hd v bits j hj := by
  induction j with
  | zero => rfl
  | succ m ih =>
    dsimp only [evolvePref]
    rw [ih (by omega)]
    have hidx : (⟨m, by omega⟩ : Fin (i + 1)) = (⟨m, hj⟩ : Fin i).castSucc := rfl
    rw [hidx, Fin.snoc_castSucc]

lemma evolvePref_eq_evolve (n d : ℕ) (hd : 0 < d) (v : Fin (2 ^ d)) (bits : Fin n → Bool)
    (j : ℕ) (hj : j ≤ n) :
    evolvePref d hd v bits j hj = evolve n d hd v bits j := by
  induction j with
  | zero => rfl
  | succ m ih =>
    dsimp only [evolvePref, evolve]
    have hmlt : m < n := by omega
    rw [ih (by omega), dite_eq_left_of_eq_true (eq_true hmlt)]

open Classical in
lemma dpRunResidues_spec (p n d : ℕ) (hd : 0 < d) (a0 r0 : ℕ)
    (loc : Fin n → Fin (2 ^ d) → Bool → Bool) (y : Fin n → Bool)
    (pref : ℕ → Bool) (s0 : Fin (2 ^ d)) :
    let D := 2 ^ d
    let w_tag := wTagOf p n d a0 pref s0
    let bitAllowed : Fin n → Bool → Bool := fun ifin b =>
      if ifin.val + d < r0 then true
      else if ifin.val + d < n then decide (b = pref (a0 * n + ifin.val + d))
      else decide (b = w_tag.val.testBit (ifin.val + d - n))
    ∀ (i : ℕ) (hi : i ≤ n) (h : Fin (D * D) → ℕ) (v_tag : Fin D),
      dpRunResidues p n d hd a0 r0 loc y pref s0 i hi h v_tag =
        (Finset.univ.filter fun x : (Fin (a0 + 1) → Fin D) × (Fin a0 → Fin i → Bool) × (Fin i → Bool) =>
          x.1 0 = s0 ∧
          uTagMatch a0 n r0 d pref (x.1 (Fin.last a0)) = true ∧
          (∀ j : Fin i, bitAllowed ⟨j.val, by omega⟩ (x.2.2 j) = true) ∧
          (∀ j : Fin i,
            xor (decide ((Finset.univ.filter fun a : Fin a0 =>
                loc ⟨j.val, by omega⟩ (evolvePref d hd (x.1 a.castSucc) (x.2.1 a) j.val (by omega)) (x.2.1 a j) = true).card % 2 = 1))
              (loc ⟨j.val, by omega⟩ (evolvePref d hd (x.1 (Fin.last a0)) x.2.2 j.val (by omega)) (x.2.2 j)) =
            xor (y ⟨j.val, by omega⟩) (highPar p n d a0 loc pref s0 ⟨j.val, by omega⟩)) ∧
          evolvePref d hd (x.1 (Fin.last a0)) x.2.2 i le_rfl = v_tag ∧
          (∀ idx : Fin (D * D),
            (Finset.univ.filter fun a : Fin a0 =>
              pairIdx D (evolvePref d hd (x.1 a.castSucc) (x.2.1 a) i le_rfl) (x.1 a.succ) = idx).card = h idx)).card := by
  intro D w_tag bitAllowed i
  induction i with
  | zero =>
    intro _ h v_tag
    dsimp only [dpRunResidues]
    by_cases hu : uTagMatch a0 n r0 d pref v_tag = true
    · rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' hu)), pathCount_spec]
      refine Finset.card_bij (fun s _ => (s, fun _ => Fin.elim0, Fin.elim0)) ?_ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        refine ⟨hs.1, by rw [hs.2.1]; exact hu, fun j => Fin.elim0 j, fun j => Fin.elim0 j, hs.2.1, hs.2.2⟩
      · intro s1 _ s2 _ heq; exact congrArg Prod.fst heq
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        refine ⟨x.1, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hx.1, hx.2.2.2.2.1, hx.2.2.2.2.2⟩
        · rcases x with ⟨x1, x21, x22⟩
          refine Prod.ext rfl (Prod.ext ?_ ?_)
          · funext _ j; exact Fin.elim0 j
          · funext j; exact Fin.elim0 j
    · rw [ite_eq_right_iff.mpr (fun h' => False.elim (hu h'))]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ hx
      have heq : x.1 (Fin.last a0) = v_tag := hx.2.2.2.2.1
      rw [heq] at hx; exact hu hx.2.1
  | succ i ih =>
    intro hi h' v_tag'
    dsimp only [dpRunResidues, dpResidueStep]
    let ifin : Fin n := ⟨i, hi⟩
    let tpar := xor (y ifin) (highPar p n d a0 loc pref s0 ifin)

    let TOf := fun v_tag : Fin D =>
      Finset.univ.filter fun x : (Fin (a0 + 1) → Fin D) × (Fin a0 → Fin i → Bool) × (Fin i → Bool) =>
        x.1 0 = s0 ∧
        uTagMatch a0 n r0 d pref (x.1 (Fin.last a0)) = true ∧
        (∀ j : Fin i, bitAllowed ⟨j.val, by omega⟩ (x.2.2 j) = true) ∧
        (∀ j : Fin i,
          xor (decide ((Finset.univ.filter fun a : Fin a0 =>
              loc ⟨j.val, by omega⟩ (evolvePref d hd (x.1 a.castSucc) (x.2.1 a) j.val (by omega)) (x.2.1 a j) = true).card % 2 = 1))
            (loc ⟨j.val, by omega⟩ (evolvePref d hd (x.1 (Fin.last a0)) x.2.2 j.val (by omega)) (x.2.2 j)) =
          xor (y ⟨j.val, by omega⟩) (highPar p n d a0 loc pref s0 ⟨j.val, by omega⟩)) ∧
        evolvePref d hd (x.1 (Fin.last a0)) x.2.2 i le_rfl = v_tag
    have hev : ∀ (v_tag : Fin D) (p_ev : Bool),
        dpInnerAux d hd a0 (loc ifin) (D * D) le_rfl
          (fun H par =>
            if par = false ∧ ∀ j : Fin (D * D), H ⟨D * D + j.val, by dsimp [D]; omega⟩ = 0 then
              dpRunResidues p n d hd a0 r0 loc y pref s0 i (by omega) (fun j => H ⟨j.val, by dsimp [D]; omega⟩) v_tag
            else 0) h' p_ev =
        ((TOf v_tag ×ˢ (Finset.univ : Finset (Fin a0 → Bool))).filter fun xb =>
          (∀ j : Fin (D * D),
            (Finset.univ.filter fun a : Fin a0 =>
              pairIdx D (nextWin d hd (evolvePref d hd (xb.1.1 a.castSucc) (xb.1.2.1 a) i le_rfl) (xb.2 a)) (xb.1.1 a.succ) = j).card = h' j) ∧
          p_ev = decide ((Finset.univ.filter fun a : Fin a0 =>
            loc ifin (evolvePref d hd (xb.1.1 a.castSucc) (xb.1.2.1 a) i le_rfl) (xb.2 a) = true).card % 2 = 1)).card := by
      intro v_tag p_ev
      have hspec := dpInnerAux_spec d hd a0 (loc ifin) (TOf v_tag)
        (fun x a => evolvePref d hd (x.1 a.castSucc) (x.2.1 a) i le_rfl)
        (fun x a => x.1 a.succ) (D * D) le_rfl h' p_ev
      have hinit_eq : (fun (H : Fin (D * D + D * D) → ℕ) (par : Bool) =>
          if par = false ∧ ∀ j : Fin (D * D), H ⟨D * D + j.val, by dsimp [D]; omega⟩ = 0 then
            dpRunResidues p n d hd a0 r0 loc y pref s0 i (by omega) (fun j => H ⟨j.val, by dsimp [D]; omega⟩) v_tag
          else 0) =
        (fun (H : Fin (D * D + D * D) → ℕ) (par : Bool) =>
          ((TOf v_tag ×ˢ (Finset.univ : Finset (Fin a0 → Bool))).filter fun xb =>
            (∀ a : Fin a0, (pairIdx D (evolvePref d hd (xb.1.1 a.castSucc) (xb.1.2.1 a) i le_rfl) (xb.1.1 a.succ)).val < D * D → xb.2 a = false) ∧
            (∀ j : Fin (D * D),
              (Finset.univ.filter fun a : Fin a0 => (pairIdx D (evolvePref d hd (xb.1.1 a.castSucc) (xb.1.2.1 a) i le_rfl) (xb.1.1 a.succ)).val = j.val).card =
                H ⟨j.val, by dsimp [D]; omega⟩) ∧
            (∀ j : Fin (D * D),
              (Finset.univ.filter fun a : Fin a0 =>
                D * D ≤ (pairIdx D (evolvePref d hd (xb.1.1 a.castSucc) (xb.1.2.1 a) i le_rfl) (xb.1.1 a.succ)).val ∧
                pairIdx D (nextWin d hd (evolvePref d hd (xb.1.1 a.castSucc) (xb.1.2.1 a) i le_rfl) (xb.2 a)) (xb.1.1 a.succ) = j).card =
                H ⟨D * D + j.val, by dsimp [D]; omega⟩) ∧
            par = decide ((Finset.univ.filter fun a : Fin a0 =>
              D * D ≤ (pairIdx D (evolvePref d hd (xb.1.1 a.castSucc) (xb.1.2.1 a) i le_rfl) (xb.1.1 a.succ)).val ∧
              loc ifin (evolvePref d hd (xb.1.1 a.castSucc) (xb.1.2.1 a) i le_rfl) (xb.2 a) = true).card % 2 = 1)).card) := by
        funext H par
        by_cases hcond : par = false ∧ ∀ j : Fin (D * D), H ⟨D * D + j.val, by dsimp [D]; omega⟩ = 0
        · rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' hcond)), ih (by omega) _ v_tag]
          refine Finset.card_bij (fun x _ => (x, fun _ => false)) ?_ ?_ ?_
          · intro x hx
            simp only [TOf, Finset.mem_filter, Finset.mem_univ, Finset.mem_product, true_and, and_true] at hx ⊢
            refine ⟨⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1⟩, fun _ _ => trivial, ?_, ?_, ?_⟩
            · intro j; simpa [Fin.ext_iff] using hx.2.2.2.2.2 j
            · intro j; rw [hcond.2 j, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro a _ ⟨hge, _⟩; exact absurd (Fin.isLt _) (Nat.not_lt.mpr hge)
            · rw [hcond.1]; symm
              have h0 : (Finset.univ.filter fun a : Fin a0 =>
                D * D ≤ (pairIdx D (evolvePref d hd (x.1 a.castSucc) (x.2.1 a) i le_rfl) (x.1 a.succ)).val ∧
                loc ifin (evolvePref d hd (x.1 a.castSucc) (x.2.1 a) i le_rfl) false = true).card = 0 := by
                rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                intro a _ ⟨hge, _⟩; exact absurd (Fin.isLt _) (Nat.not_lt.mpr hge)
              rw [h0]; rfl
          · intro x1 _ x2 _ heq; exact congrArg Prod.fst heq
          · intro xb hxb
            simp only [TOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true] at hxb
            refine ⟨xb.1, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨hxb.1.1, hxb.1.2.1, hxb.1.2.2.1, hxb.1.2.2.2.1, hxb.1.2.2.2.2, fun j => ?_⟩
              simpa [Fin.ext_iff] using hxb.2.2.1 j
            · rcases xb with ⟨xb1, xb2⟩
              refine Prod.ext rfl ?_
              funext a; exact (hxb.2.1 a (Fin.isLt _)).symm
        · rw [ite_eq_right_iff.mpr (fun h' => False.elim (hcond h'))]
          symm; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro xb _ hxb
          apply hcond
          refine ⟨?_, fun j => ?_⟩
          · rw [hxb.2.2.2]
            have h0 : (Finset.univ.filter fun a : Fin a0 =>
              D * D ≤ (pairIdx D (evolvePref d hd (xb.1.1 a.castSucc) (xb.1.2.1 a) i le_rfl) (xb.1.1 a.succ)).val ∧
              loc ifin (evolvePref d hd (xb.1.1 a.castSucc) (xb.1.2.1 a) i le_rfl) (xb.2 a) = true).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro a _ ⟨hge, _⟩; exact absurd (Fin.isLt _) (Nat.not_lt.mpr hge)
            rw [h0]; rfl
          · rw [← hxb.2.2.1 j, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro a _ ⟨hge, _⟩; exact absurd (Fin.isLt _) (Nat.not_lt.mpr hge)
      rw [hinit_eq, hspec]
      dsimp only
      congr 1; ext xb
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true, Nat.zero_le, zero_add]
      constructor
      · rintro ⟨hx, _, _, h1, h2⟩; exact ⟨hx, h1, h2⟩
      · rintro ⟨hx, h1, h2⟩; exact ⟨hx, fun _ hlt => absurd hlt (Nat.not_lt_zero _), fun j => Fin.elim0 j, h1, h2⟩

    let Big := Finset.univ.filter fun x : (Fin (a0 + 1) → Fin D) × (Fin a0 → Fin (i + 1) → Bool) × (Fin (i + 1) → Bool) =>
      x.1 0 = s0 ∧
      uTagMatch a0 n r0 d pref (x.1 (Fin.last a0)) = true ∧
      (∀ j : Fin (i + 1), bitAllowed ⟨j.val, by omega⟩ (x.2.2 j) = true) ∧
      (∀ j : Fin (i + 1),
        xor (decide ((Finset.univ.filter fun a : Fin a0 =>
            loc ⟨j.val, by omega⟩ (evolvePref d hd (x.1 a.castSucc) (x.2.1 a) j.val (by omega)) (x.2.1 a j) = true).card % 2 = 1))
          (loc ⟨j.val, by omega⟩ (evolvePref d hd (x.1 (Fin.last a0)) x.2.2 j.val (by omega)) (x.2.2 j)) =
        xor (y ⟨j.val, by omega⟩) (highPar p n d a0 loc pref s0 ⟨j.val, by omega⟩)) ∧
      evolvePref d hd (x.1 (Fin.last a0)) x.2.2 (i + 1) le_rfl = v_tag' ∧
      (∀ idx : Fin (D * D),
        (Finset.univ.filter fun a : Fin a0 =>
          pairIdx D (evolvePref d hd (x.1 a.castSucc) (x.2.1 a) (i + 1) le_rfl) (x.1 a.succ) = idx).card = h' idx)
    show _ = Big.card

    have hpart : Big.card = ∑ v_tag : Fin D, ∑ b : Bool,
        (Big.filter fun x => evolvePref d hd (x.1 (Fin.last a0)) x.2.2 i (by omega) = v_tag ∧ x.2.2 (Fin.last i) = b).card := by
      have h1 : Big.card = ∑ vb : Fin D × Bool,
          (Big.filter fun x => (evolvePref d hd (x.1 (Fin.last a0)) x.2.2 i (by omega), x.2.2 (Fin.last i)) = vb).card := by
        rw [← Finset.card_biUnion (by
          intro p1 _ p2 _ hne
          simp only [Function.onFun, Finset.disjoint_left]; intro x hx1 hx2
          simp only [Finset.mem_filter] at hx1 hx2
          exact hne (hx1.2.symm.trans hx2.2))]
        congr 1; ext x; simp
      rw [h1, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro v_tag _
      apply Finset.sum_congr rfl; intro b _
      congr 1
    rw [hpart]
    apply Finset.sum_congr rfl; intro v_tag _
    apply Finset.sum_congr rfl; intro b _
    by_cases hcond : bitAllowed ifin b = true ∧ nextWin d hd v_tag b = v_tag'
    · rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' hcond)), hev v_tag (xor tpar (loc ifin v_tag b))]
      refine Finset.card_bij
        (fun xb _ => (xb.1.1, fun a => Fin.snoc (α := fun _ => Bool) (xb.1.2.1 a) (xb.2 a),
          Fin.snoc (α := fun _ => Bool) xb.1.2.2 b)) ?_ ?_ ?_
      · intro xb hxb
        simp only [TOf, Big, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true] at hxb ⊢
        rcases hxb with ⟨⟨hs0', hu', hba', hpar', hvtag'⟩, hh', hp'⟩
        have hsnoc_tag : evolvePref d hd (xb.1.1 (Fin.last a0)) (Fin.snoc (α := fun _ => Bool) xb.1.2.2 b) i (by omega) = v_tag := by
          rw [evolvePref_snoc d hd _ _ _ i le_rfl, hvtag']
        refine ⟨⟨hs0', hu', ?_, ?_, ?_, ?_⟩, hsnoc_tag, by simp [Fin.snoc_last]⟩
        · intro j
          refine Fin.lastCases ?_ ?_ j
          · simp only [Fin.snoc_last, Fin.val_last]; exact hcond.1
          · intro j'; simp only [Fin.snoc_castSucc, Fin.val_castSucc]; exact hba' j'
        · intro j
          refine Fin.lastCases ?_ ?_ j
          · simp only [Fin.snoc_last, Fin.val_last]
            have h1 : (Finset.univ.filter fun a : Fin a0 =>
                loc ifin (evolvePref d hd (xb.1.1 a.castSucc) (Fin.snoc (α := fun _ => Bool) (xb.1.2.1 a) (xb.2 a)) i (by omega))
                  (xb.2 a) = true) =
              (Finset.univ.filter fun a : Fin a0 =>
                loc ifin (evolvePref d hd (xb.1.1 a.castSucc) (xb.1.2.1 a) i le_rfl) (xb.2 a) = true) := by
              ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              rw [evolvePref_snoc d hd _ _ _ i le_rfl]
            rw [h1, hsnoc_tag, ← hp']
            dsimp only [tpar, ifin]
            cases xor (y ⟨i, hi⟩) (highPar p n d a0 loc pref s0 ⟨i, hi⟩) <;> cases loc ⟨i, hi⟩ v_tag b <;> rfl
          · intro j'
            simp only [Fin.snoc_castSucc, Fin.val_castSucc]
            have h1 : (Finset.univ.filter fun a : Fin a0 =>
                loc ⟨j'.val, by omega⟩ (evolvePref d hd (xb.1.1 a.castSucc) (Fin.snoc (α := fun _ => Bool) (xb.1.2.1 a) (xb.2 a)) j'.val (by omega))
                  (xb.1.2.1 a j') = true) =
              (Finset.univ.filter fun a : Fin a0 =>
                loc ⟨j'.val, by omega⟩ (evolvePref d hd (xb.1.1 a.castSucc) (xb.1.2.1 a) j'.val (by omega)) (xb.1.2.1 a j') = true) := by
              ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              rw [evolvePref_snoc d hd _ _ _ j'.val (by omega)]
            rw [h1, evolvePref_snoc d hd _ _ _ j'.val (by omega)]; exact hpar' j'
        · dsimp only [evolvePref]
          rw [hsnoc_tag, show (⟨i, by omega⟩ : Fin (i + 1)) = Fin.last i from rfl, Fin.snoc_last]
          exact hcond.2
        · intro idx
          rw [← hh' idx]; congr 1; ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp only [evolvePref]
          rw [evolvePref_snoc d hd _ _ _ i le_rfl, show (⟨i, by omega⟩ : Fin (i + 1)) = Fin.last i from rfl, Fin.snoc_last]
      · intro xb1 _ xb2 _ heq
        rcases xb1 with ⟨⟨a1, b1, c1⟩, d1⟩
        rcases xb2 with ⟨⟨a2, b2, c2⟩, d2⟩
        dsimp only at heq
        have h1 : a1 = a2 := by injection heq
        have h23 : (fun a => Fin.snoc (α := fun _ => Bool) (b1 a) (d1 a), Fin.snoc (α := fun _ => Bool) c1 b) =
            (fun a => Fin.snoc (α := fun _ => Bool) (b2 a) (d2 a), Fin.snoc (α := fun _ => Bool) c2 b) := by
          injection heq
        have h2 : (fun a => Fin.snoc (α := fun _ => Bool) (b1 a) (d1 a)) =
            (fun a => Fin.snoc (α := fun _ => Bool) (b2 a) (d2 a)) := by injection h23
        have h3 : Fin.snoc (α := fun _ => Bool) c1 b = Fin.snoc (α := fun _ => Bool) c2 b := by injection h23
        refine Prod.ext (Prod.ext h1 (Prod.ext ?_ ?_)) ?_
        · funext a j; have := congrFun (congrFun h2 a) j.castSucc; simpa [Fin.snoc_castSucc] using this
        · funext j; have := congrFun h3 j.castSucc; simpa [Fin.snoc_castSucc] using this
        · funext a; have := congrFun (congrFun h2 a) (Fin.last i); simpa [Fin.snoc_last] using this
      · intro x hx
        simp only [Big, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rcases hx with ⟨⟨hs0', hu', hba', hpar', hvtag', hh'⟩, hv_prev, hb_last⟩
        refine ⟨((x.1, fun a j => x.2.1 a j.castSucc, fun j => x.2.2 j.castSucc), fun a => x.2.1 a (Fin.last i)), ?_, ?_⟩
        · have hev_eq : ∀ (v : Fin D) (f : Fin (i + 1) → Bool) (j : ℕ) (hj : j ≤ i),
              evolvePref d hd v (fun k : Fin i => f k.castSucc) j hj = evolvePref d hd v f j (by omega) := by
            intro v f j
            induction j with
            | zero => intro _; rfl
            | succ m ihm => intro hj; dsimp only [evolvePref]; rw [ihm (by omega)]; rfl
          simp only [TOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true]
          refine ⟨⟨hs0', hu', fun j => hba' j.castSucc, fun j => ?_, by rw [hev_eq]; exact hv_prev⟩, ?_, ?_⟩
          · have h1 := hpar' j.castSucc
            simpa only [hev_eq, Fin.val_castSucc] using h1
          · intro idx; rw [← hh' idx]; congr 1; ext a
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            dsimp only [evolvePref]
            rw [hev_eq]
            rfl
          · have hlast := hpar' (Fin.last i)
            simp only [Fin.val_last, hv_prev, hb_last] at hlast
            have hset : (Finset.univ.filter fun a : Fin a0 =>
                loc ifin (evolvePref d hd (x.1 a.castSucc) (fun j => x.2.1 a j.castSucc) i le_rfl) (x.2.1 a (Fin.last i)) = true) =
              (Finset.univ.filter fun a : Fin a0 =>
                loc ifin (evolvePref d hd (x.1 a.castSucc) (x.2.1 a) i (by omega)) (x.2.1 a (Fin.last i)) = true) := by
              ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hev_eq]
            rw [hset]
            have : xor (decide ((Finset.univ.filter fun a : Fin a0 =>
                loc ifin (evolvePref d hd (x.1 a.castSucc) (x.2.1 a) i (by omega)) (x.2.1 a (Fin.last i)) = true).card % 2 = 1))
                (loc ifin v_tag b) = tpar := hlast
            rw [← this]
            cases decide ((Finset.univ.filter fun a : Fin a0 =>
                loc ifin (evolvePref d hd (x.1 a.castSucc) (x.2.1 a) i (by omega)) (x.2.1 a (Fin.last i)) = true).card % 2 = 1) <;>
              cases loc ifin v_tag b <;> rfl
        · rcases x with ⟨x1, x21, x22⟩
          dsimp only at hb_last
          refine Prod.ext rfl (Prod.ext ?_ ?_)
          · funext a j
            refine Fin.lastCases (by simp [Fin.snoc_last]) (fun j' => by simp [Fin.snoc_castSucc]) j
          · funext j
            refine Fin.lastCases (by simp [Fin.snoc_last, hb_last]) (fun j' => by simp [Fin.snoc_castSucc]) j
    · rw [ite_eq_right_iff.mpr (fun h' => False.elim (hcond h'))]
      symm; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx ⟨hv_prev, hb_last⟩
      simp only [Big, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      apply hcond
      refine ⟨?_, ?_⟩
      · have := hx.2.2.1 (Fin.last i)
        simpa [Fin.val_last, hb_last] using this
      · have := hx.2.2.2.2.1
        dsimp only [evolvePref] at this
        rw [hv_prev, show (⟨i, by omega⟩ : Fin (i + 1)) = Fin.last i from rfl, hb_last] at this
        exact this

lemma isDiagHist_iff (D : ℕ) (h : Fin (D * D) → ℕ) :
    isDiagHist D h = true ↔ ∀ v w : Fin D, v ≠ w → h (pairIdx D v w) = 0 := by
  unfold isDiagHist
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro H v w hne
    rcases H v w with rfl | h0
    · exact False.elim (hne rfl)
    · exact h0
  · intro H v w
    by_cases hvw : v = w
    · exact Or.inl hvw
    · exact Or.inr (H v w hvw)

lemma s0Match_iff (m d : ℕ) (pref : ℕ → Bool) (s0 : Fin (2 ^ d)) :
    s0Match m d pref s0 = true ↔ ∀ t < d, m ≤ t → s0.val.testBit t = pref t := by
  unfold s0Match
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro H t ht hmt
    rcases H t ht with hlt | heq
    · omega
    · exact heq
  · intro H t ht
    by_cases hlt : t < m
    · exact Or.inl hlt
    · exact Or.inr (H t ht (by omega))

lemma uTagMatch_iff (a0 n r0 d : ℕ) (pref : ℕ → Bool) (u : Fin (2 ^ d)) :
    uTagMatch a0 n r0 d pref u = true ↔ ∀ t < d, r0 ≤ t → u.val.testBit t = pref (a0 * n + t) := by
  unfold uTagMatch
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro H t ht hrt
    rcases H t ht with hlt | heq
    · omega
    · exact heq
  · intro H t ht
    by_cases hlt : t < r0
    · exact Or.inl hlt
    · exact Or.inr (H t ht (by omega))

lemma highWin_testBit (k d : ℕ) (pref : ℕ → Bool) (s0 : Fin (2 ^ d)) (pos t : ℕ) (ht : t < d) :
    (highWin k d pref s0 pos).val.testBit t = highBit k d pref s0 (pos + t) := by
  dsimp only [highWin]
  have hgen : ∀ (m : ℕ) (f : Fin m → Bool) (i : ℕ) (hi : i < m),
      (∑ j : Fin m, if f j then 2 ^ j.val else 0).testBit i = f ⟨i, hi⟩ := by
    intro m; induction m with
    | zero => intro _ _ hi; omega
    | succ m ih =>
      intro f i hi
      rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
      set lo := ∑ j : Fin m, if f j.castSucc = true then 2 ^ j.val else 0
      have hlo : lo < 2 ^ m := by
        have hsum : ∀ (m' : ℕ) (g : Fin m' → Bool), (∑ j : Fin m', if g j then 2 ^ j.val else 0) < 2 ^ m' := by
          intro m'; induction m' with
          | zero => intro _; simp
          | succ m' ih' =>
            intro g; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
            have := ih' (fun j => g j.castSucc); have : 2 ^ (m' + 1) = 2 ^ m' + 2 ^ m' := by rw [pow_succ]; omega
            split_ifs <;> omega
        exact hsum m _
      by_cases him : i = m
      · subst him
        cases hf : f (Fin.last i)
        · simp [Nat.testBit_lt_two_pow hlo]; exact hf
        · simp only [↓reduceIte]
          rw [Nat.add_comm lo, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlo]; exact hf.symm
      · have hilt : i < m := by omega
        cases hf : f (Fin.last m)
        · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
          exact ih (fun j => f j.castSucc) i hilt
        · simp only [↓reduceIte]
          rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hilt]
          exact ih (fun j => f j.castSucc) i hilt
  exact hgen d (fun j => highBit k d pref s0 (pos + j.val)) t ht

open Classical in
lemma dpPrefixCount_spec (p n d : ℕ) (hp : 2 ≤ p) (hd : 0 < d) (hdn : d < n)
    (m : ℕ) (hm : m < p * n)
    (loc : Fin n → Fin (2 ^ d) → Bool → Bool) (y : Fin n → Bool) (pref : ℕ → Bool) :
    dpPrefixCount p n d hd m loc y pref =
      (Finset.univ.filter fun w : Fin (2 ^ (p * n)) =>
        prefMatch (p * n) m pref w ∧ hitLoc p n d loc y w).card := by
  unfold dpPrefixCount
  set a0 := m / n
  set r0 := m % n
  have hn : 0 < n := by omega
  have ha0 : a0 < p := (Nat.div_lt_iff_lt_mul hn).mpr hm
  have hr0 : r0 < n := Nat.mod_lt m hn
  have hm_eq : m = a0 * n + r0 := by have := Nat.div_add_mod m n; rw [Nat.mul_comm] at this; exact this.symm
  let D := 2 ^ d
  let k := p * n
  have hk : 0 < k := Nat.mul_pos (by omega) hn

  have hsum_s0 : ∀ s0 : Fin D,
      ((allHists (D * D) a0).map fun h =>
        if isDiagHist D h = true then dpRunResidues p n d hd a0 r0 loc y pref s0 n le_rfl h (wTagOf p n d a0 pref s0) else 0).sum =
      (Finset.univ.filter fun x : (Fin (a0 + 1) → Fin D) × (Fin a0 → Fin n → Bool) × (Fin n → Bool) =>
        x.1 0 = s0 ∧
        uTagMatch a0 n r0 d pref (x.1 (Fin.last a0)) = true ∧
        (∀ j : Fin n,
          (if j.val + d < r0 then true
           else if j.val + d < n then decide (x.2.2 j = pref (a0 * n + j.val + d))
           else decide (x.2.2 j = (wTagOf p n d a0 pref s0).val.testBit (j.val + d - n))) = true) ∧
        (∀ j : Fin n,
          xor (decide ((Finset.univ.filter fun a : Fin a0 =>
              loc j (evolve n d hd (x.1 a.castSucc) (x.2.1 a) j.val) (x.2.1 a j) = true).card % 2 = 1))
            (loc j (evolve n d hd (x.1 (Fin.last a0)) x.2.2 j.val) (x.2.2 j)) =
          xor (y j) (highPar p n d a0 loc pref s0 j)) ∧
        evolve n d hd (x.1 (Fin.last a0)) x.2.2 n = wTagOf p n d a0 pref s0 ∧
        (∀ a : Fin a0, evolve n d hd (x.1 a.castSucc) (x.2.1 a) n = x.1 a.succ)).card := by
    intro s0
    rw [← List.sum_toFinset _ (nodup_allHists _ _)]
    let TupSet := Finset.univ.filter fun x : (Fin (a0 + 1) → Fin D) × (Fin a0 → Fin n → Bool) × (Fin n → Bool) =>
      x.1 0 = s0 ∧
      uTagMatch a0 n r0 d pref (x.1 (Fin.last a0)) = true ∧
      (∀ j : Fin n,
        (if j.val + d < r0 then true
         else if j.val + d < n then decide (x.2.2 j = pref (a0 * n + j.val + d))
         else decide (x.2.2 j = (wTagOf p n d a0 pref s0).val.testBit (j.val + d - n))) = true) ∧
      (∀ j : Fin n,
        xor (decide ((Finset.univ.filter fun a : Fin a0 =>
            loc j (evolve n d hd (x.1 a.castSucc) (x.2.1 a) j.val) (x.2.1 a j) = true).card % 2 = 1))
          (loc j (evolve n d hd (x.1 (Fin.last a0)) x.2.2 j.val) (x.2.2 j)) =
        xor (y j) (highPar p n d a0 loc pref s0 j)) ∧
      evolve n d hd (x.1 (Fin.last a0)) x.2.2 n = wTagOf p n d a0 pref s0 ∧
      (∀ a : Fin a0, evolve n d hd (x.1 a.castSucc) (x.2.1 a) n = x.1 a.succ)
    let hOfX := fun (x : (Fin (a0 + 1) → Fin D) × (Fin a0 → Fin n → Bool) × (Fin n → Bool)) (idx : Fin (D * D)) =>
      (Finset.univ.filter fun a : Fin a0 => pairIdx D (evolve n d hd (x.1 a.castSucc) (x.2.1 a) n) (x.1 a.succ) = idx).card
    have hhOfX_sum : ∀ x, ∑ idx : Fin (D * D), hOfX x idx = a0 := by
      intro x
      rw [← Finset.card_biUnion (by
        intro i1 _ i2 _ hne
        simp only [Function.onFun, Finset.disjoint_left]; intro a ha1 ha2
        simp only [Finset.mem_filter] at ha1 ha2
        exact hne (ha1.2.symm.trans ha2.2))]
      have : (Finset.univ.biUnion fun idx : Fin (D * D) =>
          Finset.univ.filter fun a : Fin a0 => pairIdx D (evolve n d hd (x.1 a.castSucc) (x.2.1 a) n) (x.1 a.succ) = idx) =
          Finset.univ := by
        ext a; simp
      rw [this, Finset.card_univ, Fintype.card_fin]
    have hpart : TupSet.card = ∑ h ∈ (allHists (D * D) a0).toFinset, (TupSet.filter fun x => hOfX x = h).card := by
      rw [← Finset.card_biUnion (by
        intro h1 _ h2 _ hne
        simp only [Function.onFun, Finset.disjoint_left]; intro x hx1 hx2
        simp only [Finset.mem_filter] at hx1 hx2
        exact hne (hx1.2.symm.trans hx2.2))]
      congr 1; ext x
      simp only [Finset.mem_biUnion, List.mem_toFinset, mem_allHists, Finset.mem_filter]
      exact ⟨fun hx => ⟨hOfX x, hhOfX_sum x, hx, rfl⟩, fun ⟨_, _, hx, _⟩ => hx⟩
    rw [hpart]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hdiag : isDiagHist D h = true
    · rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' hdiag)), dpRunResidues_spec]
      congr 1; ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, TupSet, evolvePref_eq_evolve]
      constructor
      · rintro ⟨hs0', hu', hba', hpar', hwt', hh'⟩
        refine ⟨⟨hs0', hu', hba', hpar', hwt', fun a => ?_⟩, funext hh'⟩
        by_contra hne
        have h0 := (isDiagHist_iff D h).mp hdiag _ _ hne
        have hc := hh' (pairIdx D (evolve n d hd (x.1 a.castSucc) (x.2.1 a) n) (x.1 a.succ))
        have hpos : 0 < (Finset.univ.filter fun a' : Fin a0 =>
            pairIdx D (evolve n d hd (x.1 a'.castSucc) (x.2.1 a') n) (x.1 a'.succ) =
            pairIdx D (evolve n d hd (x.1 a.castSucc) (x.2.1 a) n) (x.1 a.succ)).card :=
          Finset.card_pos.mpr ⟨a, by simp⟩
        rw [hc, h0] at hpos; exact Nat.lt_irrefl 0 hpos
      · rintro ⟨⟨hs0', hu', hba', hpar', hwt', hcompat⟩, hheq⟩
        exact ⟨hs0', hu', hba', hpar', hwt', fun idx => congrFun hheq idx⟩
    · rw [ite_eq_right_iff.mpr (fun h' => False.elim (hdiag h'))]
      symm; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx hheq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, TupSet] at hx
      apply hdiag
      rw [isDiagHist_iff]
      intro v w hne
      rw [← hheq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a _ hpair
      have ⟨hv, hw⟩ := pairIdx_injective D _ _ _ _ hpair
      rw [hx.2.2.2.2.2 a] at hv
      exact hne (hv.symm.trans hw)

  let WSet := Finset.univ.filter fun w : Fin (2 ^ k) => prefMatch k m pref w ∧ hitLoc p n d loc y w
  have hWpart : WSet.card = ∑ s0 : Fin D, (WSet.filter fun w => winOf k d w 0 = s0).card := by
    rw [← Finset.card_biUnion (by
      intro s1 _ s2 _ hne
      simp only [Function.onFun, Finset.disjoint_left]; intro w hw1 hw2
      simp only [Finset.mem_filter] at hw1 hw2
      exact hne (hw1.2.symm.trans hw2.2))]
    congr 1; ext w; simp
  rw [hWpart]
  apply Finset.sum_congr rfl
  intro s0 _
  by_cases hs0m : s0Match m d pref s0 = true
  · rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' hs0m)), hsum_s0 s0]
    symm

    refine Finset.card_bij
      (fun w _ => (fun a : Fin (a0 + 1) => winOf k d w (a.val * n),
        fun (a : Fin a0) (j : Fin n) => w.val.testBit ((a.val * n + j.val + d) % k),
        fun j : Fin n => w.val.testBit ((a0 * n + j.val + d) % k))) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, WSet] at hw ⊢
      rcases hw with ⟨⟨hpm, hhit⟩, hwin0⟩

      have hhb : ∀ pos, m ≤ pos → pos < k + d → w.val.testBit (pos % k) = highBit k d pref s0 pos := by
        intro pos hpos1 hpos2
        dsimp only [highBit]
        have hdk : d < k := lt_of_lt_of_le hdn (Nat.le_mul_of_pos_left n (by omega))
        by_cases hlt : pos < k
        · rw [if_pos hlt, Nat.mod_eq_of_lt hlt]; exact hpm pos hpos1 hlt
        · rw [if_neg hlt]
          have hsub : pos % k = pos - k := by
            have hadd : pos - k + k = pos := by omega
            conv_lhs => rw [← hadd]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hsub, ← hwin0, winOf_testBit k d w 0 (pos - k) (by omega), zero_add, Nat.mod_eq_of_lt (by omega)]
      have hhwin : ∀ pos, m ≤ pos → pos < k → winOf k d w pos = highWin k d pref s0 pos := by
        intro pos hpos1 hpos2
        apply Fin.ext; apply Nat.eq_of_testBit_eq; intro t
        by_cases ht : t < d
        · rw [winOf_testBit k d w pos t ht, highWin_testBit k d pref s0 pos t ht]
          exact hhb (pos + t) (by omega) (by omega)
        · have h1 : (winOf k d w pos).val < 2 ^ t := lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by omega) (by omega))
          have h2 : (highWin k d pref s0 pos).val < 2 ^ t := lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by omega) (by omega))
          rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
      have hwt_eq : winOf k d w ((a0 + 1) * n) = wTagOf p n d a0 pref s0 := by
        dsimp only [wTagOf]
        by_cases ha0p : a0 + 1 < p
        · rw [if_pos ha0p]
          have hlt : (a0 + 1) * n < k := Nat.mul_lt_mul_of_pos_right ha0p hn
          have hge : m ≤ (a0 + 1) * n := by rw [hm_eq, Nat.add_mul, one_mul]; omega
          exact hhwin ((a0 + 1) * n) hge hlt
        · rw [if_neg ha0p]
          have heq : (a0 + 1) * n = k := by dsimp [k]; rw [show a0 + 1 = p by omega]
          rw [heq, ← hwin0]
          apply Fin.ext; apply Nat.eq_of_testBit_eq; intro t
          by_cases ht : t < d
          · rw [winOf_testBit k d w k t ht, winOf_testBit k d w 0 t ht, zero_add, Nat.add_mod_left]
          · have h1 : (winOf k d w k).val < 2 ^ t := lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by omega) (by omega))
            have h2 : (winOf k d w 0).val < 2 ^ t := lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by omega) (by omega))
            rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
      refine ⟨by simpa using hwin0, ?_, ?_, ?_, ?_, ?_⟩
      · rw [uTagMatch_iff]
        intro t ht hrt
        rw [Fin.val_last, winOf_testBit k d w (a0 * n) t ht]
        have hlt : a0 * n + t < k := by
          have : a0 * n + t < (a0 + 1) * n := by rw [Nat.add_mul, one_mul]; omega
          exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
        rw [Nat.mod_eq_of_lt hlt]
        exact hpm (a0 * n + t) (by omega) hlt
      · intro j
        by_cases h1 : j.val + d < r0
        · simp [h1]
        · by_cases h2 : j.val + d < n
          · simp only [h1, h2, ↓reduceIte, decide_eq_true_eq]
            have hlt : a0 * n + j.val + d < k := by
              have : a0 * n + j.val + d < (a0 + 1) * n := by rw [Nat.add_mul, one_mul]; omega
              exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
            rw [Nat.mod_eq_of_lt hlt]
            exact hpm (a0 * n + j.val + d) (by omega) hlt
          · simp only [h1, h2, ↓reduceIte, decide_eq_true_eq]
            rw [← hwt_eq, winOf_testBit k d w ((a0 + 1) * n) (j.val + d - n) (by omega)]
            have heq : a0 * n + j.val + d = (a0 + 1) * n + (j.val + d - n) := by rw [Nat.add_mul, one_mul]; omega
            rw [heq]
      · intro j
        have hhit_j := hhit j
        rw [foldl_xor_eq_parity] at hhit_j

        have hhp : highPar p n d a0 loc pref s0 j =
            decide ((Finset.univ.filter fun a : Fin p =>
              a0 < a.val ∧ loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card % 2 = 1) := by
          unfold highPar
          have hfr_eq : (List.finRange p).foldl (fun acc (a : Fin p) =>
              if a0 < a.val then xor acc (loc j (highWin k d pref s0 (a.val * n + j.val)) (highBit k d pref s0 (a.val * n + j.val + d))) else acc) false =
            (List.finRange p).foldl (fun acc (a : Fin p) =>
              xor acc (if a0 < a.val then loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) else false)) false := by
            have hcongr : ∀ (l : List (Fin p)) (acc : Bool),
                l.foldl (fun acc (a : Fin p) => if a0 < a.val then xor acc (loc j (highWin k d pref s0 (a.val * n + j.val)) (highBit k d pref s0 (a.val * n + j.val + d))) else acc) acc =
                l.foldl (fun acc (a : Fin p) => xor acc (if a0 < a.val then loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) else false)) acc := by
              intro l
              induction l with
              | nil => intro _; rfl
              | cons a t ih =>
                intro acc; simp only [List.foldl_cons]
                by_cases hgt : a0 < a.val
                · have hge1 : m ≤ a.val * n + j.val := by
                    have : (a0 + 1) * n ≤ a.val * n := Nat.mul_le_mul_right n (by omega)
                    rw [hm_eq, Nat.add_mul, one_mul] at *; omega
                  have hlt1 : a.val * n + j.val < k := by
                    have : a.val * n + j.val < (a.val + 1) * n := by rw [Nat.add_mul, one_mul]; omega
                    exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
                  rw [if_pos hgt, if_pos hgt, hhwin _ hge1 hlt1, hhb (a.val * n + j.val + d) (by omega) (by omega)]
                  exact ih _
                · rw [if_neg hgt, if_neg hgt, Bool.xor_false]; exact ih _
            exact hcongr (List.finRange p) false
          rw [hfr_eq, foldl_xor_eq_parity]
          congr 4; ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hgt : a0 < a.val <;> simp [hgt]
        have hcard_split : (Finset.univ.filter fun a : Fin p =>
            loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card =
          (Finset.univ.filter fun a : Fin a0 =>
            loc j (evolve n d hd (winOf k d w (a.val * n)) (fun j' : Fin n => w.val.testBit ((a.val * n + j'.val + d) % k)) j.val)
              (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card +
          (if loc j (evolve n d hd (winOf k d w (a0 * n)) (fun j' : Fin n => w.val.testBit ((a0 * n + j'.val + d) % k)) j.val)
              (w.val.testBit ((a0 * n + j.val + d) % k)) = true then 1 else 0) +
          (Finset.univ.filter fun a : Fin p =>
            a0 < a.val ∧ loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card := by
          have hev_a : ∀ (a : Fin p), evolve n d hd (winOf k d w (a.val * n))
              (fun j' : Fin n => w.val.testBit ((a.val * n + j'.val + d) % k)) j.val = winOf k d w (a.val * n + j.val) :=
            fun a => evolve_winOf p n d hd w a j.val (by omega)
          have h1 : (Finset.univ.filter fun a : Fin a0 =>
              loc j (evolve n d hd (winOf k d w (a.val * n)) (fun j' : Fin n => w.val.testBit ((a.val * n + j'.val + d) % k)) j.val)
                (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card =
            (Finset.univ.filter fun a : Fin p =>
              a.val < a0 ∧ loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card := by
            refine Finset.card_bij (fun a _ => ⟨a.val, by omega⟩) ?_ ?_ ?_
            · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
              exact ⟨a.isLt, by simpa only [hev_a ⟨a.val, by omega⟩] using ha⟩
            · intro a1 _ a2 _ heq; exact Fin.ext (congrArg (Fin.val (n := p)) heq)
            · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
              refine ⟨⟨a.val, ha.1⟩, ?_, Fin.ext rfl⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              simpa only [hev_a a] using ha.2
          have h2 : (if loc j (evolve n d hd (winOf k d w (a0 * n)) (fun j' : Fin n => w.val.testBit ((a0 * n + j'.val + d) % k)) j.val)
              (w.val.testBit ((a0 * n + j.val + d) % k)) = true then 1 else 0) =
            (Finset.univ.filter fun a : Fin p =>
              a.val = a0 ∧ loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card := by
            have heva0 := hev_a ⟨a0, ha0⟩
            dsimp only at heva0; rw [heva0]
            cases hl : loc j (winOf k d w (a0 * n + j.val)) (w.val.testBit ((a0 * n + j.val + d) % k))
            · simp only [Bool.false_eq_true, ↓reduceIte]
              symm; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro a _ ⟨heq, htrue⟩; rw [heq, hl] at htrue; exact Bool.false_ne_true htrue
            · simp only [↓reduceIte]
              have hsing : (Finset.univ.filter fun a : Fin p =>
                  a.val = a0 ∧ loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true) =
                  {⟨a0, ha0⟩} := by
                ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
                exact ⟨fun h => h.1, fun h => ⟨h, by rw [h]; exact hl⟩⟩
              rw [hsing, Finset.card_singleton]
          rw [h1, h2,
            ← Finset.card_union_of_disjoint (by
              rw [Finset.disjoint_left]; intro a ha1 ha2
              simp only [Finset.mem_filter] at ha1 ha2; omega),
            ← Finset.card_union_of_disjoint (by
              rw [Finset.disjoint_left]; intro a ha1 ha2
              simp only [Finset.mem_union, Finset.mem_filter] at ha1 ha2
              rcases ha1 with ha1 | ha1 <;> omega)]
          congr 1; ext a; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h; rcases lt_trichotomy a.val a0 with hlt | heq | hgt
            · exact Or.inl (Or.inl ⟨hlt, h⟩)
            · exact Or.inl (Or.inr ⟨heq, h⟩)
            · exact Or.inr ⟨hgt, h⟩
          · rintro ((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) <;> exact h
        rw [hhp, ← hhit_j, hcard_split]
        simp only [Fin.val_castSucc, Fin.val_last]
        set A := (Finset.univ.filter fun a : Fin a0 =>
            loc j (evolve n d hd (winOf k d w (a.val * n)) (fun j' : Fin n => w.val.testBit ((a.val * n + j'.val + d) % k)) j.val)
              (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card
        set C := (Finset.univ.filter fun a : Fin p =>
            a0 < a.val ∧ loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card
        cases loc j (evolve n d hd (winOf k d w (a0 * n)) (fun j' : Fin n => w.val.testBit ((a0 * n + j'.val + d) % k)) j.val)
            (w.val.testBit ((a0 * n + j.val + d) % k)) <;>
          rcases Nat.mod_two_eq_zero_or_one A with hA | hA <;>
          rcases Nat.mod_two_eq_zero_or_one C with hC | hC <;>
          simp [Nat.add_mod, hA, hC]
      · rw [Fin.val_last, evolve_winOf p n d hd w ⟨a0, ha0⟩ n le_rfl]
        have : a0 * n + n = (a0 + 1) * n := by rw [Nat.add_mul, one_mul]
        rw [this, hwt_eq]
      · intro a
        have := evolve_winOf p n d hd w ⟨a.val, by omega⟩ n le_rfl
        have hmul : a.val * n + n = (a.val + 1) * n := by rw [Nat.add_mul, one_mul]
        simpa only [Fin.val_castSucc, Fin.val_succ, hmul] using this
    ·
      intro w1 hw1 w2 hw2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, WSet] at hw1 hw2
      have hb_free : ∀ (a : Fin a0) (j : Fin n),
          w1.val.testBit ((a.val * n + j.val + d) % k) = w2.val.testBit ((a.val * n + j.val + d) % k) :=
        fun a j => congrFun (congrFun (congrArg (fun z => z.2.1) heq) a) j
      have hb_tag : ∀ (j : Fin n),
          w1.val.testBit ((a0 * n + j.val + d) % k) = w2.val.testBit ((a0 * n + j.val + d) % k) :=
        fun j => congrFun (congrArg (fun z => z.2.2) heq) j
      apply Fin.ext; apply Nat.eq_of_testBit_eq; intro pos
      by_cases hpos : pos < k
      · by_cases hge : m ≤ pos
        · rw [hw1.1.1 pos hge hpos, hw2.1.1 pos hge hpos]
        ·
          have hdk : d < k := lt_of_lt_of_le hdn (Nat.le_mul_of_pos_left n (by omega))
          by_cases hpos_d : pos < d
          · have h1 := winOf_testBit k d w1 0 pos hpos_d
            have h2 := winOf_testBit k d w2 0 pos hpos_d
            have hw10 : winOf k d w1 0 = s0 := hw1.2
            have hw20 : winOf k d w2 0 = s0 := hw2.2
            rw [hw10] at h1; rw [hw20] at h2
            rw [zero_add, Nat.mod_eq_of_lt hpos] at h1 h2
            exact h1.symm.trans h2
          · have hq_lt : pos - d < m := by omega
            have ha_lt : (pos - d) / n ≤ a0 := by
              rw [hm_eq] at hq_lt
              have : pos - d < (a0 + 1) * n := by rw [Nat.add_mul, one_mul]; omega
              have := (Nat.div_lt_iff_lt_mul hn).mpr this; omega
            have hj_lt : (pos - d) % n < n := Nat.mod_lt _ hn
            have hrecon : ((pos - d) / n * n + (pos - d) % n + d) % k = pos := by
              have := Nat.div_add_mod (pos - d) n
              rw [Nat.mul_comm] at this
              rw [this, Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hpos]
            by_cases hlt_a0 : (pos - d) / n < a0
            · have := hb_free ⟨(pos - d) / n, hlt_a0⟩ ⟨(pos - d) % n, hj_lt⟩
              simpa only [hrecon] using this
            · have ha_eq : (pos - d) / n = a0 := by omega
              have := hb_tag ⟨(pos - d) % n, hj_lt⟩
              rw [← ha_eq, hrecon] at this; exact this
      · have h1 : w1.val < 2 ^ pos := lt_of_lt_of_le w1.isLt (Nat.pow_le_pow_right (by omega) (by omega))
        have h2 : w2.val < 2 ^ pos := lt_of_lt_of_le w2.isLt (Nat.pow_le_pow_right (by omega) (by omega))
        rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    ·
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨hs0', hu', hba', hpar', hwt', hcompat⟩
      have hdk : d < k := lt_of_lt_of_le hdn (Nat.le_mul_of_pos_left n (by omega))
      let bitOf : ℕ → Bool := fun pos =>
        let q := (pos + k - d) % k
        let a := q / n
        let j := q % n
        if ha : a < a0 then x.2.1 ⟨a, ha⟩ ⟨j, Nat.mod_lt _ hn⟩
        else if a = a0 then x.2.2 ⟨j, Nat.mod_lt _ hn⟩
        else highBit k d pref s0 (a * n + j + d)
      let w : Fin (2 ^ k) := bitsToFin k bitOf

      have hw_block : ∀ (a : Fin p) (j : Fin n),
          w.val.testBit ((a.val * n + j.val + d) % k) =
            if ha : a.val < a0 then x.2.1 ⟨a.val, ha⟩ j
            else if a.val = a0 then x.2.2 j
            else highBit k d pref s0 (a.val * n + j.val + d) := by
        intro a j
        have hpos_lt : (a.val * n + j.val + d) % k < k := Nat.mod_lt _ hk
        rw [bitsToFin_testBit k bitOf _ hpos_lt]
        have hq : ((a.val * n + j.val + d) % k + k - d) % k = a.val * n + j.val := by
          have h1 : (a.val * n + j.val + d) % k + k - d = (a.val * n + j.val + d) % k + (k - d) := by omega
          rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have h2 : a.val * n + j.val + d + (k - d) = a.val * n + j.val + k := by omega
          have hlt : a.val * n + j.val < k := by
            have : a.val * n + j.val < (a.val + 1) * n := by rw [Nat.add_mul, one_mul]; omega
            exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
        have ha_div : (a.val * n + j.val) / n = a.val := by
          rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, add_zero]
        have hj_mod : (a.val * n + j.val) % n = j.val := by
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
        dsimp only [bitOf]
        simp only [hq, ha_div, hj_mod]

      have hwin_eq_a : ∀ (a : Fin (a0 + 1)), winOf k d w (a.val * n) = x.1 a := by
        intro a
        apply Fin.ext; apply Nat.eq_of_testBit_eq; intro t
        by_cases ht : t < d
        · rw [winOf_testBit k d w (a.val * n) t ht]
          by_cases ha0' : a.val = 0
          ·
            have ha_eq : a = 0 := Fin.ext ha0'
            rw [ha_eq, hs0', Fin.val_zero, zero_mul, zero_add]
            have hmod : t % k = ((p - 1) * n + (n - d + t) + d) % k := by
              have : (p - 1) * n + (n - d + t) + d = t + k := by
                have : (p - 1) * n + n = p * n := by
                  have : p = p - 1 + 1 := by omega
                  conv_rhs => rw [this, Nat.add_mul, one_mul]
                dsimp [k]; omega
              rw [this, Nat.add_mod_right]
            rw [hmod, hw_block ⟨p - 1, by omega⟩ ⟨n - d + t, by omega⟩]
            by_cases ha0p : a0 < p - 1
            · have h1 : ¬ (p - 1 < a0) := by omega
              have h2 : p - 1 ≠ a0 := by omega
              simp only [h1, h2, ↓reduceDIte, ↓reduceIte, highBit]
              have hge : ¬ ((p - 1) * n + (n - d + t) + d < k) := by
                have : (p - 1) * n + n = k := by
                  have : p = p - 1 + 1 := by omega
                  dsimp [k]; conv_rhs => rw [this, Nat.add_mul, one_mul]
                omega
              rw [if_neg hge]
              congr 1
              have : (p - 1) * n + n = k := by
                have : p = p - 1 + 1 := by omega
                dsimp [k]; conv_rhs => rw [this, Nat.add_mul, one_mul]
              omega
            · have ha0_eq : p - 1 = a0 := by omega
              have h1 : ¬ (p - 1 < a0) := by omega
              simp only [h1, ha0_eq, ↓reduceDIte, ↓reduceIte]
              have hba := hba' ⟨n - d + t, by omega⟩
              have h1' : ¬ (n - d + t + d < r0) := by omega
              have h2' : ¬ (n - d + t + d < n) := by omega
              simp only [h1', h2', ↓reduceIte, decide_eq_true_eq] at hba
              have hwt_s0 : wTagOf p n d a0 pref s0 = s0 := by
                unfold wTagOf; rw [if_neg (by omega)]
              rw [hba, hwt_s0]
              have ht_eq : n - d + t + d - n = t := by omega
              rw [ht_eq]; simp
          ·
            have hprev : a.val - 1 < a0 := by omega
            have hmod : (a.val * n + t) % k = ((a.val - 1) * n + (n - d + t) + d) % k := by
              congr 1
              have : (a.val - 1) * n + n = a.val * n := by
                have : a.val = a.val - 1 + 1 := by omega
                conv_rhs => rw [this, Nat.add_mul, one_mul]
              omega
            rw [hmod, hw_block ⟨a.val - 1, by omega⟩ ⟨n - d + t, by omega⟩]
            simp only [hprev, ↓reduceDIte]
            have hcomp := hcompat ⟨a.val - 1, hprev⟩
            have hsucc : (⟨a.val - 1, hprev⟩ : Fin a0).succ = a := Fin.ext (by dsimp; omega)
            rw [hsucc] at hcomp
            rw [← hcomp, evolve_n_testBit n d hd hdn _ _ t ht]
        · have h1 : (winOf k d w (a.val * n)).val < 2 ^ t := lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by omega) (by omega))
          have h2 : (x.1 a).val < 2 ^ t := lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by omega) (by omega))
          rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

      have hpm : prefMatch k m pref w := by
        intro pos hpos1 hpos2
        by_cases hpos_d : pos < d
        · have h0 : winOf k d w 0 = s0 := by simpa [hs0'] using hwin_eq_a 0
          have h1 := winOf_testBit k d w 0 pos hpos_d
          rw [h0, zero_add, Nat.mod_eq_of_lt hpos2] at h1
          rw [← h1]
          exact (s0Match_iff m d pref s0).mp hs0m pos hpos_d hpos1
        ·
          have hq_lt : pos - d < k := by omega
          set a := (pos - d) / n
          set j := (pos - d) % n
          have ha_lt : a < p := (Nat.div_lt_iff_lt_mul hn).mpr hq_lt
          have hj_lt : j < n := Nat.mod_lt _ hn
          have hpos_eq : a * n + j + d = pos := by
            have := Nat.div_add_mod (pos - d) n; rw [Nat.mul_comm] at this; dsimp [a, j]; omega
          have hrecon : (a * n + j + d) % k = pos := by
            rw [hpos_eq, Nat.mod_eq_of_lt hpos2]
          conv_lhs => rw [← hrecon]
          rw [hw_block ⟨a, ha_lt⟩ ⟨j, hj_lt⟩]
          by_cases ha1 : a < a0
          ·
            have ha_eq : a + 1 = a0 := by
              have : a * n + j + d < (a + 2) * n := by rw [Nat.add_mul]; nlinarith
              by_contra hne
              have hle : a + 2 ≤ a0 := by omega
              have : (a + 2) * n ≤ a0 * n := Nat.mul_le_mul_right n hle
              omega
            have hj_ge : n ≤ j + d := by
              by_contra hlt
              have : a * n + j + d < (a + 1) * n := by rw [Nat.add_mul, one_mul]; omega
              rw [ha_eq] at this; omega
            rw [dite_eq_left_of_eq_true (eq_true ha1)]
            have hcomp := hcompat ⟨a, ha1⟩
            have hsucc : (⟨a, ha1⟩ : Fin a0).succ = Fin.last a0 := Fin.ext (by dsimp; omega)
            rw [hsucc] at hcomp
            have ht_lt : j + d - n < d := by omega
            have htb := evolve_n_testBit n d hd hdn (x.1 (⟨a, ha1⟩ : Fin a0).castSucc) (x.2.1 ⟨a, ha1⟩) (j + d - n) ht_lt
            rw [hcomp] at htb
            have hj_eq : (⟨n - d + (j + d - n), by omega⟩ : Fin n) = ⟨j, hj_lt⟩ := Fin.ext (by dsimp; omega)
            rw [hj_eq] at htb
            rw [← htb]
            have hu_eq := (uTagMatch_iff a0 n r0 d pref (x.1 (Fin.last a0))).mp hu' (j + d - n) ht_lt (by
              have : a * n + n = a0 * n := by rw [← ha_eq, Nat.add_mul, one_mul]
              omega)
            rw [hu_eq]; congr 1
            have : a * n + n = a0 * n := by rw [← ha_eq, Nat.add_mul, one_mul]
            omega
          · by_cases ha2 : a = a0
            · rw [dite_eq_right_of_eq_false (eq_false ha1), ite_eq_left_iff.mpr (fun h' => False.elim (h' ha2))]
              rw [ha2] at hpos_eq
              have hba := hba' ⟨j, hj_lt⟩
              have hnot1 : ¬ (j + d < r0) := by omega
              by_cases h2 : j + d < n
              · simp only [hnot1, h2, ↓reduceIte, decide_eq_true_eq] at hba
                rw [hba, hpos_eq]
              · simp only [hnot1, h2, ↓reduceIte, decide_eq_true_eq] at hba
                have ha0p : a0 + 1 < p := by
                  have : (a0 + 1) * n ≤ pos := by rw [Nat.add_mul, one_mul]; omega
                  by_contra hge
                  have : p * n ≤ (a0 + 1) * n := Nat.mul_le_mul_right n (by omega)
                  omega
                rw [hba]; dsimp only [wTagOf]; rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' ha0p)), highWin_testBit k d pref s0 _ _ (by omega)]
                dsimp only [highBit]
                have hpos_eq' : (a0 + 1) * n + (j + d - n) = pos := by rw [Nat.add_mul, one_mul]; omega
                rw [hpos_eq', ite_eq_left_iff.mpr (fun h' => False.elim (h' hpos2))]
            · rw [dite_eq_right_of_eq_false (eq_false ha1), ite_eq_right_iff.mpr (fun h' => False.elim (ha2 h'))]
              dsimp only [highBit]
              rw [hpos_eq, ite_eq_left_iff.mpr (fun h' => False.elim (h' hpos2))]

      have hhit : hitLoc p n d loc y w := by
        intro j
        rw [foldl_xor_eq_parity]

        have hwin0 : winOf k d w 0 = s0 := by simpa [hs0'] using hwin_eq_a 0
        have hhb : ∀ pos, m ≤ pos → pos < k + d → w.val.testBit (pos % k) = highBit k d pref s0 pos := by
          intro pos hpos1 hpos2; dsimp only [highBit]
          by_cases hlt : pos < k
          · rw [if_pos hlt, Nat.mod_eq_of_lt hlt]; exact hpm pos hpos1 hlt
          · rw [if_neg hlt]
            have hsub : pos % k = pos - k := by
              have hadd : pos - k + k = pos := by omega
              conv_lhs => rw [← hadd]
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [hsub, ← hwin0, winOf_testBit k d w 0 (pos - k) (by omega), zero_add, Nat.mod_eq_of_lt (by omega)]
        have hhwin : ∀ pos, m ≤ pos → pos < k → winOf k d w pos = highWin k d pref s0 pos := by
          intro pos hpos1 hpos2
          apply Fin.ext; apply Nat.eq_of_testBit_eq; intro t
          by_cases ht : t < d
          · rw [winOf_testBit k d w pos t ht, highWin_testBit k d pref s0 pos t ht]
            exact hhb (pos + t) (by omega) (by omega)
          · have h1 : (winOf k d w pos).val < 2 ^ t := lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by omega) (by omega))
            have h2 : (highWin k d pref s0 pos).val < 2 ^ t := lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by omega) (by omega))
            rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
        have hhp : highPar p n d a0 loc pref s0 j =
            decide ((Finset.univ.filter fun a : Fin p =>
              a0 < a.val ∧ loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card % 2 = 1) := by
          unfold highPar
          have hfr_eq : (List.finRange p).foldl (fun acc (a : Fin p) =>
              if a0 < a.val then xor acc (loc j (highWin k d pref s0 (a.val * n + j.val)) (highBit k d pref s0 (a.val * n + j.val + d))) else acc) false =
            (List.finRange p).foldl (fun acc (a : Fin p) =>
              xor acc (if a0 < a.val then loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) else false)) false := by
            have hcongr : ∀ (l : List (Fin p)) (acc : Bool),
                l.foldl (fun acc (a : Fin p) => if a0 < a.val then xor acc (loc j (highWin k d pref s0 (a.val * n + j.val)) (highBit k d pref s0 (a.val * n + j.val + d))) else acc) acc =
                l.foldl (fun acc (a : Fin p) => xor acc (if a0 < a.val then loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) else false)) acc := by
              intro l; induction l with
              | nil => intro _; rfl
              | cons a t ih =>
                intro acc; simp only [List.foldl_cons]
                by_cases hgt : a0 < a.val
                · have hge1 : m ≤ a.val * n + j.val := by
                    have : (a0 + 1) * n ≤ a.val * n := Nat.mul_le_mul_right n (by omega)
                    rw [hm_eq, Nat.add_mul, one_mul] at *; omega
                  have hlt1 : a.val * n + j.val < k := by
                    have : a.val * n + j.val < (a.val + 1) * n := by rw [Nat.add_mul, one_mul]; omega
                    exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
                  rw [if_pos hgt, if_pos hgt, hhwin _ hge1 hlt1, hhb (a.val * n + j.val + d) (by omega) (by omega)]
                  exact ih _
                · rw [if_neg hgt, if_neg hgt, Bool.xor_false]; exact ih _
            exact hcongr (List.finRange p) false
          rw [hfr_eq, foldl_xor_eq_parity]
          congr 4; ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hgt : a0 < a.val <;> simp [hgt]
        have hbf_eq : ∀ (a : Fin a0), (fun j' : Fin n => w.val.testBit ((a.val * n + j'.val + d) % k)) = x.2.1 a := by
          intro a; funext j'; rw [hw_block ⟨a.val, by omega⟩ j']; simp [a.isLt]
        have hbt_eq : (fun j' : Fin n => w.val.testBit ((a0 * n + j'.val + d) % k)) = x.2.2 := by
          funext j'; rw [hw_block ⟨a0, ha0⟩ j']; simp
        have hcard_split : (Finset.univ.filter fun a : Fin p =>
            loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card =
          (Finset.univ.filter fun a : Fin a0 =>
            loc j (evolve n d hd (x.1 a.castSucc) (x.2.1 a) j.val) (x.2.1 a j) = true).card +
          (if loc j (evolve n d hd (x.1 (Fin.last a0)) x.2.2 j.val) (x.2.2 j) = true then 1 else 0) +
          (Finset.univ.filter fun a : Fin p =>
            a0 < a.val ∧ loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card := by
          have h1 : (Finset.univ.filter fun a : Fin a0 =>
              loc j (evolve n d hd (x.1 a.castSucc) (x.2.1 a) j.val) (x.2.1 a j) = true).card =
            (Finset.univ.filter fun a : Fin p =>
              a.val < a0 ∧ loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card := by
            refine Finset.card_bij (fun a _ => ⟨a.val, by omega⟩) ?_ ?_ ?_
            · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
              have hev := evolve_winOf p n d hd w ⟨a.val, by omega⟩ j.val (by omega)
              have hwa := hwin_eq_a a.castSucc
              dsimp only [Fin.val_castSucc] at hwa
              dsimp only at hev
              rw [hwa, hbf_eq a] at hev
              have hbit := congrFun (hbf_eq a) j
              exact ⟨a.isLt, by rw [← hev, hbit]; exact ha⟩
            · intro a1 _ a2 _ heq; exact Fin.ext (congrArg (Fin.val (n := p)) heq)
            · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
              let af : Fin a0 := ⟨a.val, ha.1⟩
              refine ⟨af, ?_, Fin.ext rfl⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              have hev := evolve_winOf p n d hd w a j.val (by omega)
              have hwa := hwin_eq_a af.castSucc
              dsimp only [af, Fin.val_castSucc] at hwa
              rw [hwa, hbf_eq af] at hev
              have hbit := congrFun (hbf_eq af) j
              dsimp only [af] at hbit
              rw [hev, ← hbit]; exact ha.2
          have h2 : (if loc j (evolve n d hd (x.1 (Fin.last a0)) x.2.2 j.val) (x.2.2 j) = true then 1 else 0) =
            (Finset.univ.filter fun a : Fin p =>
              a.val = a0 ∧ loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card := by
            have hev := evolve_winOf p n d hd w ⟨a0, ha0⟩ j.val (by omega)
            have hwa := hwin_eq_a (Fin.last a0); rw [Fin.val_last] at hwa
            rw [hwa, hbt_eq] at hev
            have hbit := congrFun hbt_eq j
            rw [hev, ← hbit]
            cases hl : loc j (winOf k d w (a0 * n + j.val)) (w.val.testBit ((a0 * n + j.val + d) % k))
            · simp only [Bool.false_eq_true, ↓reduceIte]
              symm; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro a _ ⟨heq, htrue⟩; rw [heq, hl] at htrue; exact Bool.false_ne_true htrue
            · simp only [↓reduceIte]
              have hsing : (Finset.univ.filter fun a : Fin p =>
                  a.val = a0 ∧ loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true) =
                  {⟨a0, ha0⟩} := by
                ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
                exact ⟨fun h => h.1, fun h => ⟨h, by rw [h]; exact hl⟩⟩
              rw [hsing, Finset.card_singleton]
          rw [h1, h2,
            ← Finset.card_union_of_disjoint (by
              rw [Finset.disjoint_left]; intro a ha1 ha2
              simp only [Finset.mem_filter] at ha1 ha2; omega),
            ← Finset.card_union_of_disjoint (by
              rw [Finset.disjoint_left]; intro a ha1 ha2
              simp only [Finset.mem_union, Finset.mem_filter] at ha1 ha2
              rcases ha1 with ha1 | ha1 <;> omega)]
          congr 1; ext a; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h; rcases lt_trichotomy a.val a0 with hlt | heq | hgt
            · exact Or.inl (Or.inl ⟨hlt, h⟩)
            · exact Or.inl (Or.inr ⟨heq, h⟩)
            · exact Or.inr ⟨hgt, h⟩
          · rintro ((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) <;> exact h
        have hpj := hpar' j
        rw [hhp] at hpj
        rw [hcard_split]
        set A := (Finset.univ.filter fun a : Fin a0 =>
            loc j (evolve n d hd (x.1 a.castSucc) (x.2.1 a) j.val) (x.2.1 a j) = true).card
        set C := (Finset.univ.filter fun a : Fin p =>
            a0 < a.val ∧ loc j (winOf k d w (a.val * n + j.val)) (w.val.testBit ((a.val * n + j.val + d) % k)) = true).card
        cases hb : loc j (evolve n d hd (x.1 (Fin.last a0)) x.2.2 j.val) (x.2.2 j) <;>
          cases hy : y j <;>
          rcases Nat.mod_two_eq_zero_or_one A with hA | hA <;>
          rcases Nat.mod_two_eq_zero_or_one C with hC | hC <;>
          simp [Nat.add_mod, hA, hC, hb, hy] at hpj ⊢
      refine ⟨w, ?_, ?_⟩
      · simp only [WSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨hpm, hhit⟩, by simpa [hs0'] using hwin_eq_a 0⟩
      · rcases x with ⟨x1, x21, x22⟩
        refine Prod.ext (funext hwin_eq_a) (Prod.ext ?_ ?_)
        · funext a j; dsimp only; rw [hw_block ⟨a.val, by omega⟩ j]; simp [a.isLt]
        · funext j; dsimp only; rw [hw_block ⟨a0, ha0⟩ j]; simp
  · rw [ite_eq_right_iff.mpr (fun h' => False.elim (hs0m h'))]
    symm; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw hwin0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, WSet] at hw
    apply hs0m
    rw [s0Match_iff]
    intro t ht hmt
    rw [← hwin0, winOf_testBit k d w 0 t ht, zero_add]
    have hlt : t < k := lt_of_lt_of_le (lt_trans ht hdn) (Nat.le_mul_of_pos_left n (by omega))
    rw [Nat.mod_eq_of_lt hlt]
    exact hw.1 t hmt hlt

lemma choose_hist_le (a0 p M B : ℕ) (ha : a0 ≤ p) (hM1 : 1 ≤ M) (hMB : M - 1 ≤ B) :
    (a0 + M - 1).choose a0 ≤ (p + B).choose p := by
  have h1 : (a0 + M - 1).choose a0 = (a0 + M - 1).choose (M - 1) := by
    have heq : a0 + M - 1 - a0 = M - 1 := by omega
    rw [← Nat.choose_symm (by omega : a0 ≤ a0 + M - 1), heq]
  have h2 : (a0 + M - 1).choose (M - 1) ≤ (p + M - 1).choose (M - 1) :=
    Nat.choose_le_choose (M - 1) (by omega)
  have h3 : (p + M - 1).choose (M - 1) = (p + M - 1).choose p := by
    have heq : p + M - 1 - (M - 1) = p := by omega
    rw [← Nat.choose_symm (by omega : M - 1 ≤ p + M - 1), heq]
  have h4 : (p + M - 1).choose p ≤ (p + B).choose p :=
    Nat.choose_le_choose p (by omega)
  omega

lemma allHists_length_le_bound (d a0 p rem : ℕ) (hd : 0 < d) (ha : a0 ≤ p)
    (hrem : rem ≤ 2 ^ d * 2 ^ d) :
    (allHists (rem + 2 ^ d * 2 ^ d) a0).length ≤ (p + (2 ^ d) ^ 3).choose p := by
  have hD2 : 2 ≤ 2 ^ d := by
    have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd
    simpa using this
  have hpos : 1 ≤ rem + 2 ^ d * 2 ^ d := by nlinarith
  rw [length_allHists _ _ hpos]
  apply choose_hist_le a0 p (rem + 2 ^ d * 2 ^ d) ((2 ^ d) ^ 3) ha hpos
  have hcube : (2 ^ d) ^ 3 = 2 ^ d * (2 ^ d * 2 ^ d) := by ring
  have hmul : 2 * (2 ^ d * 2 ^ d) ≤ 2 ^ d * (2 ^ d * 2 ^ d) := Nat.mul_le_mul_right _ hD2
  omega

lemma foldl_cstate_spec {n_in : ℕ} {α β : Type*}
    (l : List α) (step : CState n_in × β → α → CState n_in × β)
    (Inv : CState n_in → β → List α → Prop)
    (cost : ℕ)
    (hstep : ∀ s b a pref, s.Valid → a ∈ l → Inv s b pref →
      let r := step (s, b) a
      s.Ext r.1 ∧ r.1.Valid ∧ r.1.gates.length ≤ s.gates.length + cost ∧ Inv r.1 r.2 (pref ++ [a]))
    (s0 : CState n_in) (hs0 : s0.Valid) (b0 : β) (pref0 : List α) (hinv0 : Inv s0 b0 pref0) :
    let r := l.foldl step (s0, b0)
    s0.Ext r.1 ∧ r.1.Valid ∧ r.1.gates.length ≤ s0.gates.length + l.length * cost ∧ Inv r.1 r.2 (pref0 ++ l) := by
  induction l generalizing s0 b0 pref0 with
  | nil =>
    exact ⟨CState.ext_refl s0, hs0, by simp, by simpa using hinv0⟩
  | cons a t ih =>
    dsimp only [List.foldl_cons]
    have h1 := hstep s0 b0 a pref0 hs0 (by simp) hinv0
    set s1 := (step (s0, b0) a).1; set b1 := (step (s0, b0) a).2
    have hpair : step (s0, b0) a = (s1, b1) := rfl
    rw [hpair]
    have h2 := ih (fun s b a' pref hs ha' hinv => hstep s b a' pref hs (by simp [ha']) hinv)
      s1 h1.2.1 b1 (pref0 ++ [a]) h1.2.2.2
    refine ⟨CState.ext_trans h1.1 h2.1, h2.2.1, ?_, ?_⟩
    · have h1g : s1.gates.length ≤ s0.gates.length + cost := h1.2.2.1
      have h2g : (List.foldl step (s1, b1) t).1.gates.length ≤ s1.gates.length + t.length * cost := h2.2.2.1
      rw [List.length_cons, Nat.add_mul, one_mul]; omega
    · simpa [List.append_assoc] using h2.2.2.2

lemma foldl_cstate_nodup_spec {n_in : ℕ} {α β : Type*}
    (l : List α) (hnd : l.Nodup) (step : CState n_in × β → α → CState n_in × β)
    (Inv : CState n_in → β → List α → Prop)
    (cost : ℕ)
    (hstep : ∀ s b a pref, s.Valid → a ∈ l → a ∉ pref → Inv s b pref →
      let r := step (s, b) a
      s.Ext r.1 ∧ r.1.Valid ∧ r.1.gates.length ≤ s.gates.length + cost ∧ Inv r.1 r.2 (pref ++ [a]))
    (s0 : CState n_in) (hs0 : s0.Valid) (b0 : β) (pref0 : List α)
    (hdisj : ∀ a ∈ l, a ∉ pref0) (hinv0 : Inv s0 b0 pref0) :
    let r := l.foldl step (s0, b0)
    s0.Ext r.1 ∧ r.1.Valid ∧ r.1.gates.length ≤ s0.gates.length + l.length * cost ∧ Inv r.1 r.2 (pref0 ++ l) := by
  induction l generalizing s0 b0 pref0 with
  | nil =>
    exact ⟨CState.ext_refl s0, hs0, by simp, by simpa using hinv0⟩
  | cons a t ih =>
    dsimp only [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    have h1 := hstep s0 b0 a pref0 hs0 (by simp) (hdisj a (by simp)) hinv0
    set s1 := (step (s0, b0) a).1; set b1 := (step (s0, b0) a).2
    have hpair : step (s0, b0) a = (s1, b1) := rfl
    rw [hpair]
    have h2 := ih hnd.2
      (fun s b a' pref hs ha' hnotin hinv => hstep s b a' pref hs (by simp [ha']) hnotin hinv)
      s1 h1.2.1 b1 (pref0 ++ [a])
      (fun x hx hmem => by
        simp only [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | rfl
        · exact hdisj x (by simp [hx]) hmem
        · exact hnd.1 hx)
      h1.2.2.2
    refine ⟨CState.ext_trans h1.1 h2.1, h2.2.1, ?_, ?_⟩
    · have h1g : s1.gates.length ≤ s0.gates.length + cost := h1.2.2.1
      have h2g : (List.foldl step (s1, b1) t).1.gates.length ≤ s1.gates.length + t.length * cost := h2.2.2.1
      rw [List.length_cons, Nat.add_mul, one_mul]; omega
    · simpa [List.append_assoc] using h2.2.2.2

def mkMuxFinD {n_in d : ℕ} (s : CState n_in) (sel : BVec d) (vals : Fin (2 ^ d) → ℕ) :
    CState n_in × ℕ :=
  let (s0, z) := mkConst s false
  (List.finRange (2 ^ d)).foldl (fun (st : CState n_in × ℕ) (v : Fin (2 ^ d)) =>
    let (s1, eqv) := mkBvEqConstAux d st.1 sel v.val
    mkIte s1 eqv (vals v) st.2) (s0, z)

lemma mkMuxFinD_spec {n_in d : ℕ} (s : CState n_in) (hs : s.Valid)
    (sel : BVec d) (vals : Fin (2 ^ d) → ℕ)
    (hsel : ∀ i, sel i < s.nw) (hvals : ∀ v, vals v < s.nw) :
    let r := mkMuxFinD s sel vals
    s.Ext r.1 ∧ r.1.Valid ∧ r.2 < r.1.nw ∧
    r.1.gates.length ≤ s.gates.length + 1 + 2 ^ d * (2 * d + 5) ∧
    ∀ x : List Bool, x.length = n_in →
      r.1.weval x r.2 = s.weval x (vals ⟨bvVal s x sel, bvVal_lt s x sel⟩) := by
  dsimp only [mkMuxFinD]
  have h0 := mkConst_spec s hs false
  set s0 := (mkConst s false).1; set z := (mkConst s false).2
  have hfold := foldl_cstate_spec (List.finRange (2 ^ d))
    (fun (st : CState n_in × ℕ) (v : Fin (2 ^ d)) =>
      let (s1, eqv) := mkBvEqConstAux d st.1 sel v.val
      mkIte s1 eqv (vals v) st.2)
    (fun s' w pref => s.Ext s' ∧ w < s'.nw ∧
      ∀ x : List Bool, x.length = n_in →
        s'.weval x w = if (⟨bvVal s x sel, bvVal_lt s x sel⟩ : Fin (2 ^ d)) ∈ pref then
          s.weval x (vals ⟨bvVal s x sel, bvVal_lt s x sel⟩) else false)
    (2 * d + 5)
    (by
      intro s' w v pref hs' _ ⟨hext, hw, hev⟩
      have h1 := mkBvEqConst_spec d s' hs' sel v.val v.isLt (fun i => lt_of_lt_of_le (hsel i) (CState.ext_nw hext))
      set s1 := (mkBvEqConstAux d s' sel v.val).1; set eqv := (mkBvEqConstAux d s' sel v.val).2
      have hext1 : s.Ext s1 := CState.ext_trans hext h1.1
      have h2 := mkIte_spec s1 h1.2.1 eqv (vals v) w h1.2.2.1
        (lt_of_lt_of_le (hvals v) (CState.ext_nw hext1)) (lt_of_lt_of_le hw (CState.ext_nw h1.1))
      refine ⟨CState.ext_trans h1.1 h2.1, h2.2.1,
        by have := h1.2.2.2.1; have := h2.2.2.2.1; dsimp only [s1, eqv] at *; omega,
        CState.ext_trans hext1 h2.1, h2.2.2.1, ?_⟩
      intro x hx
      rw [h2.2.2.2.2 x hx, h1.2.2.2.2 x hx, bvVal_ext hext x hx sel hsel,
        CState.ext_weval hext1 x hx (vals v) (hvals v), CState.ext_weval h1.1 x hx w hw, hev x hx]
      by_cases hveq : (⟨bvVal s x sel, bvVal_lt s x sel⟩ : Fin (2 ^ d)) = v
      · have hvval : bvVal s x sel = v.val := congrArg Fin.val hveq
        simp [hvval, hveq]
      · have hvval : bvVal s x sel ≠ v.val := fun h => hveq (Fin.ext h)
        simp [hvval, hveq])
    s0 h0.2.1 z [] ⟨h0.1, h0.2.2.1, fun x hx => by simp only [List.not_mem_nil, ↓reduceIte]; exact h0.2.2.2.2 x hx⟩
  refine ⟨CState.ext_trans h0.1 hfold.1, hfold.2.1, hfold.2.2.2.2.1, ?_, ?_⟩
  · have := h0.2.2.2.1; have := hfold.2.2.1; simp only [List.length_finRange] at this
    dsimp only [s0] at *; omega
  · intro x hx
    have h := hfold.2.2.2.2.2 x hx
    simp only [List.nil_append, List.mem_finRange, ↓reduceIte] at h
    exact h

def mkBvMuxFinD {n_in d L : ℕ} (s : CState n_in) (sel : BVec d) (vals : Fin (2 ^ d) → BVec L) :
    CState n_in × BVec L :=
  let (s0, z) := mkBvConst s L 0
  (List.finRange (2 ^ d)).foldl (fun (st : CState n_in × BVec L) (v : Fin (2 ^ d)) =>
    let (s1, eqv) := mkBvEqConstAux d st.1 sel v.val
    mkBvIte L s1 eqv (vals v) st.2) (s0, z)

lemma mkBvMuxFinD_spec {n_in d L : ℕ} (s : CState n_in) (hs : s.Valid)
    (sel : BVec d) (vals : Fin (2 ^ d) → BVec L)
    (hsel : ∀ i, sel i < s.nw) (hvals : ∀ v i, vals v i < s.nw) :
    let r := mkBvMuxFinD s sel vals
    s.Ext r.1 ∧ r.1.Valid ∧ (∀ i, r.2 i < r.1.nw) ∧
    r.1.gates.length ≤ s.gates.length + 2 + 2 ^ d * (2 * d + 1 + 4 * L) ∧
    ∀ x : List Bool, x.length = n_in →
      bvVal r.1 x r.2 = bvVal s x (vals ⟨bvVal s x sel, bvVal_lt s x sel⟩) := by
  dsimp only [mkBvMuxFinD]
  have h0 := mkBvConst_spec s hs L 0
  set s0 := (mkBvConst s L 0).1; set z := (mkBvConst s L 0).2
  have hfold := foldl_cstate_spec (List.finRange (2 ^ d))
    (fun (st : CState n_in × BVec L) (v : Fin (2 ^ d)) =>
      let (s1, eqv) := mkBvEqConstAux d st.1 sel v.val
      mkBvIte L s1 eqv (vals v) st.2)
    (fun s' w pref => s.Ext s' ∧ (∀ i, w i < s'.nw) ∧
      ∀ x : List Bool, x.length = n_in →
        bvVal s' x w = if (⟨bvVal s x sel, bvVal_lt s x sel⟩ : Fin (2 ^ d)) ∈ pref then
          bvVal s x (vals ⟨bvVal s x sel, bvVal_lt s x sel⟩) else 0)
    (2 * d + 1 + 4 * L)
    (by
      intro s' w v pref hs' _ ⟨hext, hw, hev⟩
      have h1 := mkBvEqConst_spec d s' hs' sel v.val v.isLt (fun i => lt_of_lt_of_le (hsel i) (CState.ext_nw hext))
      set s1 := (mkBvEqConstAux d s' sel v.val).1; set eqv := (mkBvEqConstAux d s' sel v.val).2
      have hext1 : s.Ext s1 := CState.ext_trans hext h1.1
      have h2 := mkBvIte_spec L s1 h1.2.1 eqv (vals v) w h1.2.2.1
        (fun i => lt_of_lt_of_le (hvals v i) (CState.ext_nw hext1))
        (fun i => lt_of_lt_of_le (hw i) (CState.ext_nw h1.1))
      refine ⟨CState.ext_trans h1.1 h2.1, h2.2.1,
        by have := h1.2.2.2.1; have := h2.2.2.2.1; dsimp only [s1, eqv] at *; omega,
        CState.ext_trans hext1 h2.1, h2.2.2.1, ?_⟩
      intro x hx
      rw [h2.2.2.2.2 x hx, h1.2.2.2.2 x hx, bvVal_ext hext x hx sel hsel,
        bvVal_ext hext1 x hx (vals v) (hvals v), bvVal_ext h1.1 x hx w hw, hev x hx]
      by_cases hveq : (⟨bvVal s x sel, bvVal_lt s x sel⟩ : Fin (2 ^ d)) = v
      · have hvval : bvVal s x sel = v.val := congrArg Fin.val hveq
        simp [hvval, hveq]
      · have hvval : bvVal s x sel ≠ v.val := fun h => hveq (Fin.ext h)
        simp [hvval, hveq])
    s0 h0.2.1 z [] ⟨h0.1, h0.2.2.1, fun x hx => by simp only [List.not_mem_nil, ↓reduceIte]; rw [h0.2.2.2.2 x hx]; simp⟩
  refine ⟨CState.ext_trans h0.1 hfold.1, hfold.2.1, hfold.2.2.2.2.1, ?_, ?_⟩
  · have := h0.2.2.2.1; have := hfold.2.2.1; simp only [List.length_finRange] at this
    dsimp only [s0] at *; omega
  · intro x hx
    have h := hfold.2.2.2.2.2 x hx
    simp only [List.nil_append, List.mem_finRange, ↓reduceIte] at h
    exact h

def mkLocTable {n_in : ℕ} (n r d : ℕ)
    (nrW ncW : ℕ → ℕ) (crW ccW : Fin r → ℕ → ℕ) (bankW : Fin n → ℕ)
    (s : CState n_in) : CState n_in × (Fin n → Fin (2 ^ d) → Bool → ℕ) :=
  let (s0, z) := mkConst s false
  let triples : List (Fin n × Fin (2 ^ d) × Bool) :=
    (List.finRange n).flatMap fun i =>
      (List.finRange (2 ^ d)).flatMap fun v =>
        [(i, v, false), (i, v, true)]
  triples.foldl (fun (st : CState n_in × (Fin n → Fin (2 ^ d) → Bool → ℕ)) ivb =>
    let (s1, w) := mkLocSensorWire n r d nrW ncW crW ccW bankW ivb.1 ivb.2.1 ivb.2.2 st.1
    (s1, fun i v b => if (i, v, b) = ivb then w else st.2 i v b)) (s0, fun _ _ _ => z)

lemma mkLocTable_spec {n_in : ℕ} (n r d : ℕ)
    (nrW ncW : ℕ → ℕ) (crW ccW : Fin r → ℕ → ℕ) (bankW : Fin n → ℕ)
    (s : CState n_in) (hs : s.Valid)
    (hnr : ∀ u, nrW u < s.nw) (hnc : ∀ u, ncW u < s.nw)
    (hcr : ∀ j u, crW j u < s.nw) (hcc : ∀ j u, ccW j u < s.nw) (hbW : ∀ i, bankW i < s.nw) :
    let res := mkLocTable n r d nrW ncW crW ccW bankW s
    s.Ext res.1 ∧ res.1.Valid ∧ (∀ i v b, res.2 i v b < res.1.nw) ∧
    res.1.gates.length ≤ s.gates.length + 1 + 2 * n * 2 ^ d * (2 * (6 + 48 * r) * (7 * r + 2) + 4) ∧
    ∀ x : List Bool, x.length = n_in → ∀ i v b,
      res.1.weval x (res.2 i v b) =
        locSensor n r d (s.weval x (bankW i))
          (fun u => s.weval x (if s.weval x (bankW i) then ncW u else nrW u))
          (fun j u => s.weval x (if s.weval x (bankW i) then ccW j u else crW j u))
          i.val v b := by
  dsimp only [mkLocTable]
  have h0 := mkConst_spec s hs false
  set s0 := (mkConst s false).1; set z := (mkConst s false).2
  set triples : List (Fin n × Fin (2 ^ d) × Bool) :=
    (List.finRange n).flatMap fun i => (List.finRange (2 ^ d)).flatMap fun v => [(i, v, false), (i, v, true)]
  have hlen : triples.length = 2 * n * 2 ^ d := by
    simp only [triples, List.length_flatMap, List.length_cons, List.length_nil, List.map_const',
      List.length_finRange, List.sum_replicate, smul_eq_mul]
    ring
  have hmem : ∀ i v b, (i, v, b) ∈ triples := by
    intro i v b
    simp only [triples, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨i, v, ?_⟩
    cases b <;> simp
  have hfold := foldl_cstate_spec triples
    (fun (st : CState n_in × (Fin n → Fin (2 ^ d) → Bool → ℕ)) ivb =>
      let (s1, w) := mkLocSensorWire n r d nrW ncW crW ccW bankW ivb.1 ivb.2.1 ivb.2.2 st.1
      (s1, fun i v b => if (i, v, b) = ivb then w else st.2 i v b))
    (fun s' tab pref => s.Ext s' ∧ (∀ i v b, tab i v b < s'.nw) ∧
      ∀ x : List Bool, x.length = n_in → ∀ i v b, (i, v, b) ∈ pref →
        s'.weval x (tab i v b) =
          locSensor n r d (s.weval x (bankW i))
            (fun u => s.weval x (if s.weval x (bankW i) then ncW u else nrW u))
            (fun j u => s.weval x (if s.weval x (bankW i) then ccW j u else crW j u))
            i.val v b)
    (2 * (6 + 48 * r) * (7 * r + 2) + 4)
    (by
      intro s' tab ivb pref hs' _ ⟨hext, htab, hev⟩
      have h1 := mkLocSensorWire_spec n r d nrW ncW crW ccW bankW ivb.1 ivb.2.1 ivb.2.2 s' hs'
        (fun u => lt_of_lt_of_le (hnr u) (CState.ext_nw hext))
        (fun u => lt_of_lt_of_le (hnc u) (CState.ext_nw hext))
        (fun j u => lt_of_lt_of_le (hcr j u) (CState.ext_nw hext))
        (fun j u => lt_of_lt_of_le (hcc j u) (CState.ext_nw hext))
        (lt_of_lt_of_le (hbW ivb.1) (CState.ext_nw hext))
      refine ⟨h1.1, h1.2.1, h1.2.2.2.1, CState.ext_trans hext h1.1, ?_, ?_⟩
      · intro i v b; dsimp only; split_ifs
        · exact h1.2.2.1
        · exact lt_of_lt_of_le (htab i v b) (CState.ext_nw h1.1)
      · intro x hx i v b hmemp
        dsimp only
        by_cases heq : (i, v, b) = ivb
        · rw [if_pos heq]
          subst heq
          rw [h1.2.2.2.2 x hx, CState.ext_weval hext x hx (bankW i) (hbW i)]
          have hnm : (fun u => s'.weval x (if s.weval x (bankW i) = true then ncW u else nrW u)) =
              (fun u => s.weval x (if s.weval x (bankW i) = true then ncW u else nrW u)) := by
            funext u; split_ifs
            · exact CState.ext_weval hext x hx _ (hnc u)
            · exact CState.ext_weval hext x hx _ (hnr u)
          have hcm : (fun j u => s'.weval x (if s.weval x (bankW i) = true then ccW j u else crW j u)) =
              (fun j u => s.weval x (if s.weval x (bankW i) = true then ccW j u else crW j u)) := by
            funext j u; split_ifs
            · exact CState.ext_weval hext x hx _ (hcc j u)
            · exact CState.ext_weval hext x hx _ (hcr j u)
          rw [hnm, hcm]
        · rw [if_neg heq, CState.ext_weval h1.1 x hx _ (htab i v b)]
          simp only [List.mem_append, List.mem_singleton, heq, or_false] at hmemp
          exact hev x hx i v b hmemp)
    s0 h0.2.1 (fun _ _ _ => z) [] ⟨h0.1, fun _ _ _ => h0.2.2.1, fun _ _ _ _ _ h => nomatch h⟩
  refine ⟨CState.ext_trans h0.1 hfold.1, hfold.2.1, hfold.2.2.2.2.1, ?_, ?_⟩
  · have := h0.2.2.2.1; have := hfold.2.2.1; rw [hlen] at this; dsimp only [s0] at *; omega
  · intro x hx i v b
    exact hfold.2.2.2.2.2 x hx i v b (by simp [hmem])

def mkHighParW {n_in : ℕ} (p n d a0 : ℕ) (i : Fin n) (locW : Fin (2 ^ d) → Bool → ℕ)
    (prefW : ℕ → ℕ) (s0 : Fin (2 ^ d)) (s : CState n_in) : CState n_in × ℕ :=
  let k := p * n
  let (s1, w0) := mkConst s false
  let (s2, w1) := mkConst s1 true
  let hbW := fun pos => if pos < k then prefW pos else if s0.val.testBit (pos - k) then w1 else w0
  (List.finRange p).foldl (fun (st : CState n_in × ℕ) (a : Fin p) =>
    if a0 < a.val then
      let winW : BVec d := fun t => hbW (a.val * n + i.val + t.val)
      let bW := hbW (a.val * n + i.val + d)
      let (sa, valF) := mkMuxFinD st.1 winW (fun v => locW v false)
      let (sb, valT) := mkMuxFinD sa winW (fun v => locW v true)
      let (sc, val) := mkIte sb bW valT valF
      mkXor sc st.2 val
    else st) (s2, w0)

lemma mkHighParW_spec {n_in : ℕ} (p n d a0 : ℕ) (i : Fin n)
    (locW : Fin (2 ^ d) → Bool → ℕ) (prefW : ℕ → ℕ) (s0 : Fin (2 ^ d))
    (s : CState n_in) (hs : s.Valid)
    (hloc : ∀ v b, locW v b < s.nw) (hpref : ∀ pos < p * n, prefW pos < s.nw) :
    let res := mkHighParW p n d a0 i locW prefW s0 s
    s.Ext res.1 ∧ res.1.Valid ∧ res.2 < res.1.nw ∧
    res.1.gates.length ≤ s.gates.length + 2 + p * (2 * (1 + 2 ^ d * (2 * d + 5)) + 9) ∧
    ∀ x : List Bool, x.length = n_in →
      res.1.weval x res.2 =
        highPar p n d a0 (fun _ v b => s.weval x (locW v b)) (fun pos => s.weval x (prefW pos)) s0 i := by
  dsimp only [mkHighParW]
  have hc0 := mkConst_spec s hs false
  set s1 := (mkConst s false).1; set w0 := (mkConst s false).2
  have hc1 := mkConst_spec s1 hc0.2.1 true
  set s2 := (mkConst s1 true).1; set w1 := (mkConst s1 true).2
  have h02 : s.Ext s2 := CState.ext_trans hc0.1 hc1.1
  let hbW := fun pos => if pos < p * n then prefW pos else if s0.val.testBit (pos - p * n) then w1 else w0
  have hhb_lt : ∀ pos, hbW pos < s2.nw := by
    intro pos; dsimp only [hbW]
    split_ifs with hlt
    · exact lt_of_lt_of_le (hpref pos hlt) (CState.ext_nw h02)
    · exact hc1.2.2.1
    · exact lt_of_lt_of_le hc0.2.2.1 (CState.ext_nw hc1.1)
  have hhb_ev : ∀ x : List Bool, x.length = n_in → ∀ pos,
      s2.weval x (hbW pos) = highBit (p * n) d (fun u => s.weval x (prefW u)) s0 pos := by
    intro x hx pos; dsimp only [hbW, highBit]
    split_ifs with hlt htb
    · exact CState.ext_weval h02 x hx (prefW pos) (hpref pos hlt)
    · rw [hc1.2.2.2.2 x hx]; exact htb.symm
    · rw [CState.ext_weval hc1.1 x hx w0 hc0.2.2.1, hc0.2.2.2.2 x hx]
      exact (Bool.eq_false_iff.mpr htb).symm
  have hfold := foldl_cstate_spec (List.finRange p)
    (fun (st : CState n_in × ℕ) (a : Fin p) =>
      if a0 < a.val then
        let winW : BVec d := fun t => hbW (a.val * n + i.val + t.val)
        let bW := hbW (a.val * n + i.val + d)
        let (sa, valF) := mkMuxFinD st.1 winW (fun v => locW v false)
        let (sb, valT) := mkMuxFinD sa winW (fun v => locW v true)
        let (sc, val) := mkIte sb bW valT valF
        mkXor sc st.2 val
      else st)
    (fun s' acc pref => s2.Ext s' ∧ acc < s'.nw ∧
      ∀ x : List Bool, x.length = n_in →
        s'.weval x acc = pref.foldl (fun b (a : Fin p) =>
          if a0 < a.val then
            xor b (s.weval x (locW (highWin (p * n) d (fun u => s.weval x (prefW u)) s0 (a.val * n + i.val))
              (highBit (p * n) d (fun u => s.weval x (prefW u)) s0 (a.val * n + i.val + d))))
          else b) false)
    (2 * (1 + 2 ^ d * (2 * d + 5)) + 9)
    (by
      intro s' acc a pref hs' _ ⟨hext, hacc, hev⟩
      by_cases hgt : a0 < a.val
      · rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' hgt))]
        let winW : BVec d := fun t => hbW (a.val * n + i.val + t.val)
        let bW := hbW (a.val * n + i.val + d)
        have h0s' : s.Ext s' := CState.ext_trans h02 hext
        have ha := mkMuxFinD_spec s' hs' winW (fun v => locW v false)
          (fun t => lt_of_lt_of_le (hhb_lt _) (CState.ext_nw hext))
          (fun v => lt_of_lt_of_le (hloc v false) (CState.ext_nw h0s'))
        set sa := (mkMuxFinD s' winW (fun v => locW v false)).1
        set valF := (mkMuxFinD s' winW (fun v => locW v false)).2
        have h2a : s2.Ext sa := CState.ext_trans hext ha.1
        have h0a : s.Ext sa := CState.ext_trans h02 h2a
        have hb := mkMuxFinD_spec sa ha.2.1 winW (fun v => locW v true)
          (fun t => lt_of_lt_of_le (hhb_lt _) (CState.ext_nw h2a))
          (fun v => lt_of_lt_of_le (hloc v true) (CState.ext_nw h0a))
        set sb := (mkMuxFinD sa winW (fun v => locW v true)).1
        set valT := (mkMuxFinD sa winW (fun v => locW v true)).2
        have h2b : s2.Ext sb := CState.ext_trans h2a hb.1
        have hc := mkIte_spec sb hb.2.1 bW valT valF
          (lt_of_lt_of_le (hhb_lt _) (CState.ext_nw h2b))
          hb.2.2.1 (lt_of_lt_of_le ha.2.2.1 (CState.ext_nw hb.1))
        set sc := (mkIte sb bW valT valF).1
        set val := (mkIte sb bW valT valF).2
        have hs'c : s'.Ext sc := CState.ext_trans ha.1 (CState.ext_trans hb.1 hc.1)
        have hd' := mkXor_spec sc hc.2.1 acc val (lt_of_lt_of_le hacc (CState.ext_nw hs'c)) hc.2.2.1
        refine ⟨CState.ext_trans hs'c hd'.1, hd'.2.1, ?_, CState.ext_trans hext (CState.ext_trans hs'c hd'.1), hd'.2.2.1, ?_⟩
        · have := ha.2.2.2.1; have := hb.2.2.2.1; have := hc.2.2.2.1; have := hd'.2.2.2.1
          dsimp only [sa, sb, sc, valF, valT, val, winW, bW] at *; omega
        · intro x hx
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ite_eq_left_iff.mpr (fun h' => False.elim (h' hgt)),
            hd'.2.2.2.2 x hx, CState.ext_weval hs'c x hx acc hacc, hev x hx,
            hc.2.2.2.2 x hx, CState.ext_weval h2b x hx bW (hhb_lt _), hhb_ev x hx _,
            hb.2.2.2.2 x hx, CState.ext_weval hb.1 x hx valF ha.2.2.1, ha.2.2.2.2 x hx]
          have hwin_val : (⟨bvVal s' x winW, bvVal_lt s' x winW⟩ : Fin (2 ^ d)) =
              highWin (p * n) d (fun u => s.weval x (prefW u)) s0 (a.val * n + i.val) := by
            apply Fin.ext; dsimp only [bvVal, highWin]
            apply Finset.sum_congr rfl; intro t _
            rw [CState.ext_weval hext x hx (winW t) (hhb_lt _), hhb_ev x hx _]
          have hwin_val2 : (⟨bvVal sa x winW, bvVal_lt sa x winW⟩ : Fin (2 ^ d)) =
              highWin (p * n) d (fun u => s.weval x (prefW u)) s0 (a.val * n + i.val) := by
            apply Fin.ext; dsimp only
            rw [bvVal_ext ha.1 x hx winW (fun t => lt_of_lt_of_le (hhb_lt _) (CState.ext_nw hext))]
            exact congrArg Fin.val hwin_val
          rw [hwin_val, hwin_val2,
            CState.ext_weval h0s' x hx _ (hloc _ false), CState.ext_weval h0a x hx _ (hloc _ true)]
          cases highBit (p * n) d (fun u => s.weval x (prefW u)) s0 (a.val * n + i.val + d) <;> rfl
      · rw [ite_eq_right_iff.mpr (fun h' => False.elim (hgt h'))]
        refine ⟨CState.ext_refl s', hs', by dsimp only; omega, hext, hacc, ?_⟩
        intro x hx
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ite_eq_right_iff.mpr (fun h' => False.elim (hgt h')), hev x hx])
    s2 hc1.2.1 w0 [] ⟨CState.ext_refl s2, lt_of_lt_of_le hc0.2.2.1 (CState.ext_nw hc1.1),
      fun x hx => by rw [CState.ext_weval hc1.1 x hx w0 hc0.2.2.1, hc0.2.2.2.2 x hx]; rfl⟩
  refine ⟨CState.ext_trans h02 hfold.1, hfold.2.1, hfold.2.2.2.2.1, ?_, ?_⟩
  · have := hc0.2.2.2.1; have := hc1.2.2.2.1; have := hfold.2.2.1
    simp only [List.length_finRange] at this; dsimp only [s1, s2, w0, w1, hbW] at *; omega
  · intro x hx
    have h := hfold.2.2.2.2.2 x hx
    simpa [highPar] using h

def mkS0MatchW {n_in : ℕ} (m d : ℕ) (prefW : ℕ → ℕ) (s0 : Fin (2 ^ d)) (s : CState n_in) : CState n_in × ℕ :=
  let (s1, w1) := mkConst s true
  (List.range d).foldl (fun (st : CState n_in × ℕ) (t : ℕ) =>
    if t < m then st
    else
      let (sa, cb) := mkConst st.1 (s0.val.testBit t)
      let (sb, eqb) := mkEq sa cb (prefW t)
      mkAnd sb st.2 eqb) (s1, w1)

lemma mkS0MatchW_spec {n_in : ℕ} (m d : ℕ) (prefW : ℕ → ℕ) (s0 : Fin (2 ^ d))
    (s : CState n_in) (hs : s.Valid) (hpref : ∀ t < d, m ≤ t → prefW t < s.nw) :
    let res := mkS0MatchW m d prefW s0 s
    s.Ext res.1 ∧ res.1.Valid ∧ res.2 < res.1.nw ∧
    res.1.gates.length ≤ s.gates.length + 1 + d * 8 ∧
    ∀ x : List Bool, x.length = n_in →
      res.1.weval x res.2 = s0Match m d (fun pos => s.weval x (prefW pos)) s0 := by
  dsimp only [mkS0MatchW]
  have h0 := mkConst_spec s hs true
  set s1 := (mkConst s true).1; set w1 := (mkConst s true).2
  have hfold := foldl_cstate_spec (List.range d)
    (fun (st : CState n_in × ℕ) (t : ℕ) =>
      if t < m then st
      else
        let (sa, cb) := mkConst st.1 (s0.val.testBit t)
        let (sb, eqb) := mkEq sa cb (prefW t)
        mkAnd sb st.2 eqb)
    (fun s' acc pref => s.Ext s' ∧ acc < s'.nw ∧
      ∀ x : List Bool, x.length = n_in →
        s'.weval x acc = pref.all (fun t => decide (t < m) || decide (s0.val.testBit t = s.weval x (prefW t))))
    8
    (by
      intro s' acc t pref hs' ht ⟨hext, hacc, hev⟩
      rw [List.mem_range] at ht
      by_cases hlt : t < m
      · rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' hlt))]
        refine ⟨CState.ext_refl s', hs', by dsimp only; omega, hext, hacc, ?_⟩
        intro x hx; simp [hev x hx, hlt]
      · rw [ite_eq_right_iff.mpr (fun h' => False.elim (hlt h'))]
        have ha := mkConst_spec s' hs' (s0.val.testBit t)
        set sa := (mkConst s' (s0.val.testBit t)).1; set cb := (mkConst s' (s0.val.testBit t)).2
        have h0a : s.Ext sa := CState.ext_trans hext ha.1
        have hb := mkEq_spec sa ha.2.1 cb (prefW t) ha.2.2.1
          (lt_of_lt_of_le (hpref t ht (by omega)) (CState.ext_nw h0a))
        set sb := (mkEq sa cb (prefW t)).1; set eqb := (mkEq sa cb (prefW t)).2
        have hs'b : s'.Ext sb := CState.ext_trans ha.1 hb.1
        have hc := mkAnd_spec sb hb.2.1 acc eqb (lt_of_lt_of_le hacc (CState.ext_nw hs'b)) hb.2.2.1
        refine ⟨CState.ext_trans hs'b hc.1, hc.2.1,
          by have := ha.2.2.2.1; have := hb.2.2.2.1; have := hc.2.2.2.1; dsimp only [sa, sb, cb, eqb] at *; omega,
          CState.ext_trans hext (CState.ext_trans hs'b hc.1), hc.2.2.1, ?_⟩
        intro x hx
        rw [hc.2.2.2.2 x hx, CState.ext_weval hs'b x hx acc hacc, hev x hx,
          hb.2.2.2.2 x hx, ha.2.2.2.2 x hx, CState.ext_weval h0a x hx (prefW t) (hpref t ht (by omega))]
        simp [hlt])
    s1 h0.2.1 w1 [] ⟨h0.1, h0.2.2.1, fun x hx => by simp only [List.all_nil]; exact h0.2.2.2.2 x hx⟩
  refine ⟨CState.ext_trans h0.1 hfold.1, hfold.2.1, hfold.2.2.2.2.1, ?_, ?_⟩
  · have := h0.2.2.2.1; have := hfold.2.2.1; simp only [List.length_range] at this
    dsimp only [s1] at *; omega
  · intro x hx; simpa [s0Match] using hfold.2.2.2.2.2 x hx

def mkUTagMatchW {n_in : ℕ} (a0 n r0 d : ℕ) (prefW : ℕ → ℕ) (u : Fin (2 ^ d)) (s : CState n_in) : CState n_in × ℕ :=
  mkS0MatchW r0 d (fun t => prefW (a0 * n + t)) u s

lemma mkUTagMatchW_spec {n_in : ℕ} (a0 n r0 d : ℕ) (prefW : ℕ → ℕ) (u : Fin (2 ^ d))
    (s : CState n_in) (hs : s.Valid) (hpref : ∀ t < d, r0 ≤ t → prefW (a0 * n + t) < s.nw) :
    let res := mkUTagMatchW a0 n r0 d prefW u s
    s.Ext res.1 ∧ res.1.Valid ∧ res.2 < res.1.nw ∧
    res.1.gates.length ≤ s.gates.length + 1 + d * 8 ∧
    ∀ x : List Bool, x.length = n_in →
      res.1.weval x res.2 = uTagMatch a0 n r0 d (fun pos => s.weval x (prefW pos)) u :=
  mkS0MatchW_spec r0 d (fun t => prefW (a0 * n + t)) u s hs hpref

def mkBinStep {n_in : ℕ} (d : ℕ) (hd : 0 < d) (a0 L : ℕ)
    (locW_i : Fin (2 ^ d) → Bool → ℕ) (rem : ℕ) (hrem : rem < 2 ^ d * 2 ^ d)
    (tab : (Fin (rem + 1 + 2 ^ d * 2 ^ d) → ℕ) → Bool → BVec L)
    (s : CState n_in) : CState n_in × ((Fin (rem + 2 ^ d * 2 ^ d) → ℕ) → Bool → BVec L) :=
  let (s0, zeroBv) := mkBvConst s L 0
  let (s1, w0) := mkConst s0 false
  let D := 2 ^ d
  let v : Fin D := ⟨rem / D, Nat.div_lt_of_lt_mul hrem⟩
  (allHists (rem + 1 + D * D) a0).foldl (fun (st : CState n_in × ((Fin (rem + D * D) → ℕ) → Bool → BVec L)) h =>
    let c := h ⟨rem, by omega⟩
    (List.range (c + 1)).foldl (fun (st' : CState n_in × ((Fin (rem + D * D) → ℕ) → Bool → BVec L)) c0 =>
      let h' := stepHist d hd rem hrem h c0
      let mult := c.choose c0
      let c1 := c - c0
      let p0 := if c0 % 2 = 1 then locW_i v false else w0
      let p1 := if c1 % 2 = 1 then locW_i v true else w0
      let (sa, pfW) := mkXor st'.1 p0 p1
      let (sb, valF) := mkBvIte L sa pfW (tab h true) (tab h false)
      let (sc, scF) := mkBvScale sb mult valF
      let (sd, addF) := mkBvAdd sc (st'.2 h' false) scF
      let (se, valT) := mkBvIte L sd pfW (tab h false) (tab h true)
      let (sf, scT) := mkBvScale se mult valT
      let (sg, addT) := mkBvAdd sf (st'.2 h' true) scT
      (sg, fun hh p => if hh = h' then (if p then addT else addF) else st'.2 hh p)
    ) st
  ) (s1, fun _ _ => zeroBv)

lemma mkBinStep_spec {n_in : ℕ} (d : ℕ) (hd : 0 < d) (a0 L : ℕ)
    (locW_i : Fin (2 ^ d) → Bool → ℕ) (rem : ℕ) (hrem : rem < 2 ^ d * 2 ^ d)
    (tab : (Fin (rem + 1 + 2 ^ d * 2 ^ d) → ℕ) → Bool → BVec L)
    (dpTab : List Bool → (Fin (rem + 1 + 2 ^ d * 2 ^ d) → ℕ) → Bool → ℕ)
    (s : CState n_in) (hs : s.Valid)
    (hloc : ∀ v b, locW_i v b < s.nw)
    (htab : ∀ h p i, tab h p i < s.nw)
    (htab_ev : ∀ x : List Bool, x.length = n_in → ∀ h p, bvVal s x (tab h p) = dpTab x h p % 2 ^ L) :
    let res := mkBinStep d hd a0 L locW_i rem hrem tab s
    s.Ext res.1 ∧ res.1.Valid ∧ (∀ hh p i, res.2 hh p i < res.1.nw) ∧
    res.1.gates.length ≤ s.gates.length + 3 + (allHists (rem + 1 + 2 ^ d * 2 ^ d) a0).length * ((a0 + 1) * (40 * (L + 1) ^ 2)) ∧
    ∀ x : List Bool, x.length = n_in → ∀ hh p,
      bvVal res.1 x (res.2 hh p) =
        dpBinStep d hd a0 (fun v b => s.weval x (locW_i v b)) rem hrem (dpTab x) hh p % 2 ^ L := by
  dsimp only [mkBinStep]
  have hz := mkBvConst_spec s hs L 0
  set s0 := (mkBvConst s L 0).1; set zeroBv := (mkBvConst s L 0).2
  have hc0 := mkConst_spec s0 hz.2.1 false
  set s1 := (mkConst s0 false).1; set w0 := (mkConst s0 false).2
  have h01 : s.Ext s1 := CState.ext_trans hz.1 hc0.1
  let D := 2 ^ d
  let v : Fin D := ⟨rem / D, Nat.div_lt_of_lt_mul hrem⟩

  let dpInnerStep := fun (x : List Bool) (h : Fin (rem + 1 + D * D) → ℕ)
      (acc : (Fin (rem + D * D) → ℕ) → Bool → ℕ) (c0 : ℕ) =>
    let c := h ⟨rem, by dsimp [D]; omega⟩
    let h' := stepHist d hd rem hrem h c0
    let mult := c.choose c0
    let pf := stepPar d rem hrem (fun v' b' => s.weval x (locW_i v' b')) c0 (c - c0)
    fun hh p => acc hh p + if hh = h' then mult * dpTab x h (xor p pf) else 0
  let dpOuterStep := fun (x : List Bool) (acc : (Fin (rem + D * D) → ℕ) → Bool → ℕ)
      (h : Fin (rem + 1 + D * D) → ℕ) =>
    (List.range (h ⟨rem, by dsimp [D]; omega⟩ + 1)).foldl (dpInnerStep x h) acc
  have hfold := foldl_cstate_spec (allHists (rem + 1 + D * D) a0)
    (fun (st : CState n_in × ((Fin (rem + D * D) → ℕ) → Bool → BVec L)) h =>
      let c := h ⟨rem, by dsimp [D]; omega⟩
      (List.range (c + 1)).foldl (fun (st' : CState n_in × ((Fin (rem + D * D) → ℕ) → Bool → BVec L)) c0 =>
        let h' := stepHist d hd rem hrem h c0
        let mult := c.choose c0
        let c1 := c - c0
        let p0 := if c0 % 2 = 1 then locW_i v false else w0
        let p1 := if c1 % 2 = 1 then locW_i v true else w0
        let (sa, pfW) := mkXor st'.1 p0 p1
        let (sb, valF) := mkBvIte L sa pfW (tab h true) (tab h false)
        let (sc, scF) := mkBvScale sb mult valF
        let (sd, addF) := mkBvAdd sc (st'.2 h' false) scF
        let (se, valT) := mkBvIte L sd pfW (tab h false) (tab h true)
        let (sf, scT) := mkBvScale se mult valT
        let (sg, addT) := mkBvAdd sf (st'.2 h' true) scT
        (sg, fun hh p => if hh = h' then (if p then addT else addF) else st'.2 hh p)
      ) st)
    (fun s' acc pref => s1.Ext s' ∧ (∀ hh p i, acc hh p i < s'.nw) ∧
      ∀ x : List Bool, x.length = n_in → ∀ hh p,
        bvVal s' x (acc hh p) = (pref.foldl (dpOuterStep x) (fun _ _ => 0) hh p) % 2 ^ L)
    ((a0 + 1) * (40 * (L + 1) ^ 2))
    (by
      intro s' acc h pref hs' hh_mem ⟨hext, hacc, hev⟩
      have hsum_h : ∑ j, h j = a0 := (mem_allHists _ _ h).mp hh_mem
      have hc_le : h ⟨rem, by dsimp [D]; omega⟩ ≤ a0 := by
        rw [← hsum_h]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      let c := h ⟨rem, by dsimp [D]; omega⟩
      have hinner := foldl_cstate_spec (List.range (c + 1))
        (fun (st' : CState n_in × ((Fin (rem + D * D) → ℕ) → Bool → BVec L)) c0 =>
          let h' := stepHist d hd rem hrem h c0
          let mult := c.choose c0
          let c1 := c - c0
          let p0 := if c0 % 2 = 1 then locW_i v false else w0
          let p1 := if c1 % 2 = 1 then locW_i v true else w0
          let (sa, pfW) := mkXor st'.1 p0 p1
          let (sb, valF) := mkBvIte L sa pfW (tab h true) (tab h false)
          let (sc, scF) := mkBvScale sb mult valF
          let (sd, addF) := mkBvAdd sc (st'.2 h' false) scF
          let (se, valT) := mkBvIte L sd pfW (tab h false) (tab h true)
          let (sf, scT) := mkBvScale se mult valT
          let (sg, addT) := mkBvAdd sf (st'.2 h' true) scT
          (sg, fun hh p => if hh = h' then (if p then addT else addF) else st'.2 hh p))
        (fun s'' acc' cpref => s'.Ext s'' ∧ (∀ hh p i, acc' hh p i < s''.nw) ∧
          ∀ x : List Bool, x.length = n_in → ∀ hh p,
            bvVal s'' x (acc' hh p) =
              (cpref.foldl (dpInnerStep x h) (pref.foldl (dpOuterStep x) (fun _ _ => 0)) hh p) % 2 ^ L)
        (40 * (L + 1) ^ 2)
        (by
          intro s'' acc' c0 cpref hs'' _ ⟨hext', hacc', hev'⟩
          have h1s'' : s1.Ext s'' := CState.ext_trans hext hext'
          have h0s'' : s.Ext s'' := CState.ext_trans h01 h1s''
          let h' := stepHist d hd rem hrem h c0
          let mult := c.choose c0
          let c1 := c - c0
          let p0 := if c0 % 2 = 1 then locW_i v false else w0
          let p1 := if c1 % 2 = 1 then locW_i v true else w0
          have hp0_lt : p0 < s''.nw := by
            dsimp only [p0]; split_ifs
            · exact lt_of_lt_of_le (hloc v false) (CState.ext_nw h0s'')
            · exact lt_of_lt_of_le hc0.2.2.1 (CState.ext_nw h1s'')
          have hp1_lt : p1 < s''.nw := by
            dsimp only [p1]; split_ifs
            · exact lt_of_lt_of_le (hloc v true) (CState.ext_nw h0s'')
            · exact lt_of_lt_of_le hc0.2.2.1 (CState.ext_nw h1s'')
          have ha := mkXor_spec s'' hs'' p0 p1 hp0_lt hp1_lt
          set sa := (mkXor s'' p0 p1).1; set pfW := (mkXor s'' p0 p1).2
          have h0a : s.Ext sa := CState.ext_trans h0s'' ha.1
          have hb := mkBvIte_spec L sa ha.2.1 pfW (tab h true) (tab h false) ha.2.2.1
            (fun i => lt_of_lt_of_le (htab h true i) (CState.ext_nw h0a))
            (fun i => lt_of_lt_of_le (htab h false i) (CState.ext_nw h0a))
          set sb := (mkBvIte L sa pfW (tab h true) (tab h false)).1
          set valF := (mkBvIte L sa pfW (tab h true) (tab h false)).2
          have hc' := mkBvScale_spec sb hb.2.1 mult valF hb.2.2.1
          set sc := (mkBvScale sb mult valF).1; set scF := (mkBvScale sb mult valF).2
          have hs''c : s''.Ext sc := CState.ext_trans ha.1 (CState.ext_trans hb.1 hc'.1)
          have hd' := mkBvAdd_spec sc hc'.2.1 (acc' h' false) scF
            (fun i => lt_of_lt_of_le (hacc' h' false i) (CState.ext_nw hs''c)) hc'.2.2.1
          set sd := (mkBvAdd sc (acc' h' false) scF).1; set addF := (mkBvAdd sc (acc' h' false) scF).2
          have had : sa.Ext sd := CState.ext_trans hb.1 (CState.ext_trans hc'.1 hd'.1)
          have h0d : s.Ext sd := CState.ext_trans h0a had
          have he := mkBvIte_spec L sd hd'.2.1 pfW (tab h false) (tab h true)
            (lt_of_lt_of_le ha.2.2.1 (CState.ext_nw had))
            (fun i => lt_of_lt_of_le (htab h false i) (CState.ext_nw h0d))
            (fun i => lt_of_lt_of_le (htab h true i) (CState.ext_nw h0d))
          set se := (mkBvIte L sd pfW (tab h false) (tab h true)).1
          set valT := (mkBvIte L sd pfW (tab h false) (tab h true)).2
          have hf := mkBvScale_spec se he.2.1 mult valT he.2.2.1
          set sf := (mkBvScale se mult valT).1; set scT := (mkBvScale se mult valT).2
          have hs''f : s''.Ext sf := CState.ext_trans hs''c (CState.ext_trans hd'.1 (CState.ext_trans he.1 hf.1))
          have hg := mkBvAdd_spec sf hf.2.1 (acc' h' true) scT
            (fun i => lt_of_lt_of_le (hacc' h' true i) (CState.ext_nw hs''f)) hf.2.2.1
          set sg := (mkBvAdd sf (acc' h' true) scT).1; set addT := (mkBvAdd sf (acc' h' true) scT).2
          have hdg : sd.Ext sg := CState.ext_trans he.1 (CState.ext_trans hf.1 hg.1)
          have hs''g : s''.Ext sg := CState.ext_trans hs''f hg.1
          refine ⟨hs''g, hg.2.1, ?_, CState.ext_trans hext' hs''g, ?_, ?_⟩
          · have h1 := ha.2.2.2.1; have h2 := hb.2.2.2.1; have h3 := hc'.2.2.2.1; have h4 := hd'.2.2.2.1
            have h5 := he.2.2.2.1; have h6 := hf.2.2.2.1; have h7 := hg.2.2.2.1
            have hquad : 5 + 2 * (4 * L + (2 + L * (13 * L + 2)) + (13 * L + 1)) ≤ 40 * (L + 1) ^ 2 := by
              have hsq : (L + 1) ^ 2 = L * L + 2 * L + 1 := by ring
              have hmul : L * (13 * L + 2) = 13 * (L * L) + 2 * L := by ring
              omega
            dsimp only [sa, sb, sc, sd, se, sf, sg, pfW, valF, scF, addF, valT, scT, addT, p0, p1, c1, mult, h', c, v, D] at *
            omega
          · intro hh p i
            dsimp only
            by_cases hhh : hh = h'
            · rw [if_pos hhh]
              cases p
              · exact lt_of_lt_of_le (hd'.2.2.1 i) (CState.ext_nw hdg)
              · exact hg.2.2.1 i
            · rw [if_neg hhh]
              exact lt_of_lt_of_le (hacc' hh p i) (CState.ext_nw hs''g)
          · intro x hx hh p
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            dsimp only [dpInnerStep]
            have hpf_ev : sa.weval x pfW = stepPar d rem hrem (fun v' b' => s.weval x (locW_i v' b')) c0 c1 := by
              rw [ha.2.2.2.2 x hx]; dsimp only [p0, p1, stepPar, v, D]
              congr 1
              · by_cases h0m : c0 % 2 = 1
                · simp only [h0m, ↓reduceIte, decide_true, Bool.true_and]
                  exact CState.ext_weval h0s'' x hx _ (hloc _ false)
                · simp only [h0m, ↓reduceIte, decide_false, Bool.false_and]
                  rw [CState.ext_weval h1s'' x hx w0 hc0.2.2.1, hc0.2.2.2.2 x hx]
              · by_cases h1m : c1 % 2 = 1
                · simp only [h1m, ↓reduceIte, decide_true, Bool.true_and]
                  exact CState.ext_weval h0s'' x hx _ (hloc _ true)
                · simp only [h1m, ↓reduceIte, decide_false, Bool.false_and]
                  rw [CState.ext_weval h1s'' x hx w0 hc0.2.2.1, hc0.2.2.2.2 x hx]
            by_cases hhh : hh = h'
            · rw [if_pos hhh, if_pos hhh]
              cases p
              · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_xor]
                rw [bvVal_ext hdg x hx addF hd'.2.2.1, hd'.2.2.2.2 x hx,
                  bvVal_ext hs''c x hx (acc' h' false) (hacc' h' false), hev' x hx h' false,
                  hc'.2.2.2.2 x hx, hb.2.2.2.2 x hx, hpf_ev,
                  bvVal_ext h0a x hx (tab h true) (htab h true),
                  bvVal_ext h0a x hx (tab h false) (htab h false),
                  htab_ev x hx h true, htab_ev x hx h false, hhh]
                cases stepPar d rem hrem (fun v' b' => s.weval x (locW_i v' b')) c0 c1 <;>
                  simp only [↓reduceIte, Bool.false_eq_true] <;>
                  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]
              · simp only [↓reduceIte, Bool.true_xor]
                rw [hg.2.2.2.2 x hx, bvVal_ext hs''f x hx (acc' h' true) (hacc' h' true), hev' x hx h' true,
                  hf.2.2.2.2 x hx, he.2.2.2.2 x hx, CState.ext_weval had x hx pfW ha.2.2.1, hpf_ev,
                  bvVal_ext h0d x hx (tab h false) (htab h false),
                  bvVal_ext h0d x hx (tab h true) (htab h true),
                  htab_ev x hx h false, htab_ev x hx h true, hhh]
                cases stepPar d rem hrem (fun v' b' => s.weval x (locW_i v' b')) c0 c1 <;>
                  simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false] <;>
                  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]
            · rw [if_neg hhh, if_neg hhh, add_zero, bvVal_ext hs''g x hx (acc' hh p) (hacc' hh p), hev' x hx hh p])
        s' hs' acc [] ⟨CState.ext_refl s', hacc, fun x hx hh p => by simpa using hev x hx hh p⟩
      refine ⟨hinner.1, hinner.2.1, ?_, CState.ext_trans hext hinner.1, hinner.2.2.2.2.1, ?_⟩
      · have := hinner.2.2.1; simp only [List.length_range] at this
        have hmul : (c + 1) * (40 * (L + 1) ^ 2) ≤ (a0 + 1) * (40 * (L + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
        dsimp only [c, D] at *; omega
      · intro x hx hh p
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simpa [dpOuterStep] using hinner.2.2.2.2.2 x hx hh p)
    s1 hc0.2.1 (fun _ _ => zeroBv) [] ⟨CState.ext_refl s1,
      fun _ _ i => lt_of_lt_of_le (hz.2.2.1 i) (CState.ext_nw hc0.1),
      fun x hx hh p => by rw [bvVal_ext hc0.1 x hx zeroBv hz.2.2.1, hz.2.2.2.2 x hx]; simp⟩
  refine ⟨CState.ext_trans h01 hfold.1, hfold.2.1, hfold.2.2.2.2.1, ?_, ?_⟩
  · have := hz.2.2.2.1; have := hc0.2.2.2.1; have := hfold.2.2.1
    dsimp only [s0, s1, zeroBv, w0, D, v] at *; omega
  · intro x hx hh p
    simpa [dpBinStep, dpOuterStep, dpInnerStep] using hfold.2.2.2.2.2 x hx hh p

def mkInnerAux {n_in : ℕ} (d : ℕ) (hd : 0 < d) (a0 L : ℕ)
    (locW_i : Fin (2 ^ d) → Bool → ℕ) :
    (rem : ℕ) → (rem ≤ 2 ^ d * 2 ^ d) →
    ((Fin (rem + 2 ^ d * 2 ^ d) → ℕ) → Bool → BVec L) →
    CState n_in → CState n_in × ((Fin (2 ^ d * 2 ^ d) → ℕ) → Bool → BVec L)
  | 0, _, tab, s => (s, fun h p => tab (fun j => h ⟨j.val, by omega⟩) p)
  | rem + 1, hle, tab, s =>
    let (s1, tab1) := mkBinStep d hd a0 L locW_i rem (by omega) tab s
    mkInnerAux d hd a0 L locW_i rem (by omega) tab1 s1

lemma mkInnerAux_spec {n_in : ℕ} (d : ℕ) (hd : 0 < d) (a0 p L : ℕ) (ha0 : a0 ≤ p)
    (locW_i : Fin (2 ^ d) → Bool → ℕ)
    (rem : ℕ) (hle : rem ≤ 2 ^ d * 2 ^ d)
    (tab : (Fin (rem + 2 ^ d * 2 ^ d) → ℕ) → Bool → BVec L)
    (dpTab : List Bool → (Fin (rem + 2 ^ d * 2 ^ d) → ℕ) → Bool → ℕ)
    (s : CState n_in) (hs : s.Valid)
    (hloc : ∀ v b, locW_i v b < s.nw)
    (htab : ∀ h q i, tab h q i < s.nw)
    (htab_ev : ∀ x : List Bool, x.length = n_in → ∀ h q, bvVal s x (tab h q) = dpTab x h q % 2 ^ L) :
    let res := mkInnerAux d hd a0 L locW_i rem hle tab s
    s.Ext res.1 ∧ res.1.Valid ∧ (∀ hh q i, res.2 hh q i < res.1.nw) ∧
    res.1.gates.length ≤ s.gates.length + rem * (3 + ((p + (2 ^ d) ^ 3).choose p) * ((p + 1) * (40 * (L + 1) ^ 2))) ∧
    ∀ x : List Bool, x.length = n_in → ∀ hh q,
      bvVal res.1 x (res.2 hh q) =
        dpInnerAux d hd a0 (fun v b => s.weval x (locW_i v b)) rem hle (dpTab x) hh q % 2 ^ L := by
  induction rem generalizing s with
  | zero =>
    refine ⟨CState.ext_refl s, hs, fun hh q i => htab _ q i, by simp [mkInnerAux], ?_⟩
    intro x hx hh q
    exact htab_ev x hx _ q
  | succ rem ih =>
    dsimp only [mkInnerAux, dpInnerAux]
    have h1 := mkBinStep_spec d hd a0 L locW_i rem (by omega) tab dpTab s hs hloc htab htab_ev
    set s1 := (mkBinStep d hd a0 L locW_i rem (by omega) tab s).1
    set tab1 := (mkBinStep d hd a0 L locW_i rem (by omega) tab s).2
    have h2 := ih (by omega) tab1
      (fun x => dpBinStep d hd a0 (fun v b => s.weval x (locW_i v b)) rem (by omega) (dpTab x))
      s1 h1.2.1
      (fun v b => lt_of_lt_of_le (hloc v b) (CState.ext_nw h1.1))
      h1.2.2.1 h1.2.2.2.2
    refine ⟨CState.ext_trans h1.1 h2.1, h2.2.1, h2.2.2.1, ?_, ?_⟩
    · have hlen := allHists_length_le_bound d a0 p (rem + 1) hd ha0 hle
      have hcost : (allHists (rem + 1 + 2 ^ d * 2 ^ d) a0).length * ((a0 + 1) * (40 * (L + 1) ^ 2)) ≤
          ((p + (2 ^ d) ^ 3).choose p) * ((p + 1) * (40 * (L + 1) ^ 2)) :=
        Nat.mul_le_mul hlen (Nat.mul_le_mul_right _ (by omega))
      have := h1.2.2.2.1; have := h2.2.2.2.1; dsimp only [s1] at *
      rw [Nat.add_mul, one_mul]; omega
    · intro x hx hh q
      rw [h2.2.2.2.2 x hx hh q]
      have hloc_eq : (fun v b => s1.weval x (locW_i v b)) = (fun v b => s.weval x (locW_i v b)) :=
        funext fun v => funext fun b => CState.ext_weval h1.1 x hx (locW_i v b) (hloc v b)
      rw [hloc_eq]

def mkResidueStep {n_in : ℕ} (p n d : ℕ) (hd : 0 < d) (a0 r0 L : ℕ)
    (locW_i : Fin (2 ^ d) → Bool → ℕ) (prefW : ℕ → ℕ) (s0 : Fin (2 ^ d))
    (i : Fin n) (tparW : ℕ)
    (dpW : (Fin (2 ^ d * 2 ^ d) → ℕ) → Fin (2 ^ d) → BVec L)
    (s : CState n_in) : CState n_in × ((Fin (2 ^ d * 2 ^ d) → ℕ) → Fin (2 ^ d) → BVec L) :=
  let D := 2 ^ d
  let (s0', zeroBv) := mkBvConst s L 0
  let (s1, w0) := mkConst s0' false
  let (s2, w1) := mkConst s1 true

  let wTagBitW : ℕ → ℕ := fun t =>
    if a0 + 1 < p then prefW ((a0 + 1) * n + t)
    else if s0.val.testBit t then w1 else w0

  let mkAllowedW : CState n_in → Bool → CState n_in × ℕ := fun st b =>
    if i.val + d < r0 then (st, w1)
    else if i.val + d < n then
      if b then (st, prefW (a0 * n + i.val + d)) else mkNot st (prefW (a0 * n + i.val + d))
    else
      if b then (st, wTagBitW (i.val + d - n)) else mkNot st (wTagBitW (i.val + d - n))

  (List.finRange D).foldl (fun (st : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) (v_tag : Fin D) =>
    let initTab : (Fin (D * D + D * D) → ℕ) → Bool → BVec L := fun H par =>
      if par = false ∧ ∀ j : Fin (D * D), H ⟨D * D + j.val, by dsimp [D]; omega⟩ = 0 then
        dpW (fun j => H ⟨j.val, by dsimp [D]; omega⟩) v_tag
      else zeroBv
    let (sa, evTab) := mkInnerAux d hd a0 L locW_i (D * D) le_rfl initTab st.1
    ([false, true] : List Bool).foldl (fun (st2 : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) (b : Bool) =>
      let (sb, allowW) := mkAllowedW st2.1 b
      let (sc, needParW) := mkXor sb tparW (locW_i v_tag b)
      let v_tag' := nextWin d hd v_tag b
      (allHists (D * D) a0).foldl (fun (st3 : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) h' =>
        let (sd, rawVal) := mkBvIte L st3.1 needParW (evTab h' true) (evTab h' false)
        let (se, gatedVal) := mkBvIte L sd allowW rawVal zeroBv
        let (sf, sumVal) := mkBvAdd se (st3.2 h' v_tag') gatedVal
        (sf, fun hh vt => if hh = h' ∧ vt = v_tag' then sumVal else st3.2 hh vt)
      ) (sc, st2.2)
    ) (sa, st.2)
  ) (s2, fun _ _ => zeroBv)

lemma mkResidueStep_spec {n_in : ℕ} (p n d : ℕ) (hd : 0 < d) (hdn : d < n) (a0 r0 L : ℕ)
    (ha0 : a0 < p) (locW_i : Fin (2 ^ d) → Bool → ℕ) (prefW : ℕ → ℕ) (s0 : Fin (2 ^ d))
    (i : Fin n) (tparW : ℕ)
    (dpW : (Fin (2 ^ d * 2 ^ d) → ℕ) → Fin (2 ^ d) → BVec L)
    (dpTab : List Bool → (Fin (2 ^ d * 2 ^ d) → ℕ) → Fin (2 ^ d) → ℕ)
    (s : CState n_in) (hs : s.Valid)
    (hloc : ∀ v b, locW_i v b < s.nw)
    (hpref : ∀ pos < p * n, prefW pos < s.nw)
    (htpar : tparW < s.nw)
    (hdp : ∀ h vt j, dpW h vt j < s.nw)
    (hdp_ev : ∀ x : List Bool, x.length = n_in → ∀ h vt, bvVal s x (dpW h vt) = dpTab x h vt % 2 ^ L) :
    let D := 2 ^ d
    let H_b := (p + D ^ 3).choose p
    let res := mkResidueStep p n d hd a0 r0 L locW_i prefW s0 i tparW dpW s
    s.Ext res.1 ∧ res.1.Valid ∧ (∀ hh vt j, res.2 hh vt j < res.1.nw) ∧
    res.1.gates.length ≤ s.gates.length + 4 + D * (D * D * (3 + H_b * ((p + 1) * (40 * (L + 1) ^ 2))) + 2 * (6 + H_b * (21 * L + 1))) ∧
    ∀ x : List Bool, x.length = n_in → ∀ hh ∈ allHists (D * D) a0, ∀ vt : Fin D,
      bvVal res.1 x (res.2 hh vt) =
        dpResidueStep p n d hd a0 r0 (fun v b => s.weval x (locW_i v b))
          (fun pos => s.weval x (prefW pos)) s0 i (s.weval x tparW) (dpTab x) hh vt % 2 ^ L := by
  intro D H_b
  dsimp only [mkResidueStep]
  have hz := mkBvConst_spec s hs L 0
  set s0' := (mkBvConst s L 0).1; set zeroBv := (mkBvConst s L 0).2
  have hc0 := mkConst_spec s0' hz.2.1 false
  set s1 := (mkConst s0' false).1; set w0 := (mkConst s0' false).2
  have hc1 := mkConst_spec s1 hc0.2.1 true
  set s2 := (mkConst s1 true).1; set w1 := (mkConst s1 true).2
  have h02 : s.Ext s2 := CState.ext_trans hz.1 (CState.ext_trans hc0.1 hc1.1)
  have hzero_s2 : ∀ j, zeroBv j < s2.nw := fun j => lt_of_lt_of_le (hz.2.2.1 j) (CState.ext_nw (CState.ext_trans hc0.1 hc1.1))
  have hzero_ev : ∀ x : List Bool, x.length = n_in → bvVal s2 x zeroBv = 0 := by
    intro x hx; rw [bvVal_ext (CState.ext_trans hc0.1 hc1.1) x hx zeroBv hz.2.2.1, hz.2.2.2.2 x hx]; simp
  let wTagBitW : ℕ → ℕ := fun t =>
    if a0 + 1 < p then prefW ((a0 + 1) * n + t)
    else if s0.val.testBit t then w1 else w0
  have hwTag_lt : ∀ t < d, wTagBitW t < s2.nw := by
    intro t ht; dsimp only [wTagBitW]
    split_ifs with hlt
    · have hpos : (a0 + 1) * n + t < p * n := by
        have : (a0 + 1) * n + t < (a0 + 2) * n := by rw [Nat.add_mul]; nlinarith
        exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
      exact lt_of_lt_of_le (hpref _ hpos) (CState.ext_nw h02)
    · exact hc1.2.2.1
    · exact lt_of_lt_of_le hc0.2.2.1 (CState.ext_nw hc1.1)
  have hwTag_ev : ∀ x : List Bool, x.length = n_in → ∀ t < d,
      s2.weval x (wTagBitW t) = (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0).val.testBit t := by
    intro x hx t ht; dsimp only [wTagBitW, wTagOf]
    split_ifs with hlt htb
    · have hpos : (a0 + 1) * n + t < p * n := by
        have : (a0 + 1) * n + t < (a0 + 2) * n := by rw [Nat.add_mul]; nlinarith
        exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
      rw [highWin_testBit (p * n) d _ s0 _ t ht, CState.ext_weval h02 x hx _ (hpref _ hpos)]
      dsimp only [highBit]; rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' hpos))]
    · rw [hc1.2.2.2.2 x hx]; exact htb.symm
    · rw [CState.ext_weval hc1.1 x hx w0 hc0.2.2.1, hc0.2.2.2.2 x hx]
      exact (Bool.eq_false_iff.mpr htb).symm
  let mkAllowedW : CState n_in → Bool → CState n_in × ℕ := fun st b =>
    if i.val + d < r0 then (st, w1)
    else if i.val + d < n then
      if b then (st, prefW (a0 * n + i.val + d)) else mkNot st (prefW (a0 * n + i.val + d))
    else
      if b then (st, wTagBitW (i.val + d - n)) else mkNot st (wTagBitW (i.val + d - n))
  have hAllow_spec : ∀ (st : CState n_in) (hst : st.Valid) (h2st : s2.Ext st) (b : Bool),
      let r := mkAllowedW st b
      st.Ext r.1 ∧ r.1.Valid ∧ r.2 < r.1.nw ∧ r.1.gates.length ≤ st.gates.length + 1 ∧
      ∀ x : List Bool, x.length = n_in →
        r.1.weval x r.2 =
          if i.val + d < r0 then true
          else if i.val + d < n then decide (b = s.weval x (prefW (a0 * n + i.val + d)))
          else decide (b = (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0).val.testBit (i.val + d - n)) := by
    intro st hst h2st b
    dsimp only [mkAllowedW]
    have h0st : s.Ext st := CState.ext_trans h02 h2st
    by_cases h1 : i.val + d < r0
    · simp only [h1, ↓reduceIte]
      refine ⟨CState.ext_refl st, hst, lt_of_lt_of_le hc1.2.2.1 (CState.ext_nw h2st), by omega, ?_⟩
      intro x hx; rw [CState.ext_weval h2st x hx w1 hc1.2.2.1, hc1.2.2.2.2 x hx]
    · by_cases h2 : i.val + d < n
      · simp only [h1, h2, ↓reduceIte]
        have hpos : a0 * n + i.val + d < p * n := by
          have : a0 * n + i.val + d < (a0 + 1) * n := by rw [Nat.add_mul, one_mul]; omega
          exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hn := mkNot_spec st hst (prefW (a0 * n + i.val + d)) (lt_of_lt_of_le (hpref _ hpos) (CState.ext_nw h0st))
          refine ⟨hn.1, hn.2.1, hn.2.2.1, by omega, ?_⟩
          intro x hx; rw [hn.2.2.2.2 x hx, CState.ext_weval h0st x hx _ (hpref _ hpos)]
          cases s.weval x (prefW (a0 * n + i.val + d)) <;> rfl
        · simp only [↓reduceIte]
          refine ⟨CState.ext_refl st, hst, lt_of_lt_of_le (hpref _ hpos) (CState.ext_nw h0st), by omega, ?_⟩
          intro x hx; rw [CState.ext_weval h0st x hx _ (hpref _ hpos)]
          cases s.weval x (prefW (a0 * n + i.val + d)) <;> rfl
      · simp only [h1, h2, ↓reduceIte]
        have ht : i.val + d - n < d := by omega
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hn := mkNot_spec st hst (wTagBitW (i.val + d - n)) (lt_of_lt_of_le (hwTag_lt _ ht) (CState.ext_nw h2st))
          refine ⟨hn.1, hn.2.1, hn.2.2.1, by omega, ?_⟩
          intro x hx; rw [hn.2.2.2.2 x hx, CState.ext_weval h2st x hx _ (hwTag_lt _ ht), hwTag_ev x hx _ ht]
          cases (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0).val.testBit (i.val + d - n) <;> rfl
        · simp only [↓reduceIte]
          refine ⟨CState.ext_refl st, hst, lt_of_lt_of_le (hwTag_lt _ ht) (CState.ext_nw h2st), by omega, ?_⟩
          intro x hx; rw [CState.ext_weval h2st x hx _ (hwTag_lt _ ht), hwTag_ev x hx _ ht]
          cases (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0).val.testBit (i.val + d - n) <;> rfl

  let bitAllowedFn := fun (x : List Bool) (b : Bool) =>
    if i.val + d < r0 then true
    else if i.val + d < n then decide (b = s.weval x (prefW (a0 * n + i.val + d)))
    else decide (b = (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0).val.testBit (i.val + d - n))
  let evolvedFn := fun (x : List Bool) (v_tag : Fin D) =>
    dpInnerAux d hd a0 (fun v b => s.weval x (locW_i v b)) (D * D) le_rfl
      (fun H par =>
        if par = false ∧ ∀ j : Fin (D * D), H ⟨D * D + j.val, by dsimp [D]; omega⟩ = 0 then
          dpTab x (fun j => H ⟨j.val, by dsimp [D]; omega⟩) v_tag
        else 0)
  have hHlen : (allHists (D * D) a0).length ≤ H_b := by
    have h := allHists_length_le_bound d a0 p 0 hd (by omega) (by omega)
    rw [zero_add] at h; exact h
  have hfold := foldl_cstate_spec (List.finRange D)
    (fun (st : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) (v_tag : Fin D) =>
      let initTab : (Fin (D * D + D * D) → ℕ) → Bool → BVec L := fun H par =>
        if par = false ∧ ∀ j : Fin (D * D), H ⟨D * D + j.val, by dsimp [D]; omega⟩ = 0 then
          dpW (fun j => H ⟨j.val, by dsimp [D]; omega⟩) v_tag
        else zeroBv
      let (sa, evTab) := mkInnerAux d hd a0 L locW_i (D * D) le_rfl initTab st.1
      ([false, true] : List Bool).foldl (fun (st2 : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) (b : Bool) =>
        let (sb, allowW) := mkAllowedW st2.1 b
        let (sc, needParW) := mkXor sb tparW (locW_i v_tag b)
        let v_tag' := nextWin d hd v_tag b
        (allHists (D * D) a0).foldl (fun (st3 : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) h' =>
          let (sd, rawVal) := mkBvIte L st3.1 needParW (evTab h' true) (evTab h' false)
          let (se, gatedVal) := mkBvIte L sd allowW rawVal zeroBv
          let (sf, sumVal) := mkBvAdd se (st3.2 h' v_tag') gatedVal
          (sf, fun hh vt => if hh = h' ∧ vt = v_tag' then sumVal else st3.2 hh vt)
        ) (sc, st2.2)
      ) (sa, st.2))
    (fun s' acc vpref => s2.Ext s' ∧ (∀ hh vt j, acc hh vt j < s'.nw) ∧
      ∀ x : List Bool, x.length = n_in → ∀ hh ∈ allHists (D * D) a0, ∀ vt : Fin D,
        bvVal s' x (acc hh vt) =
          (vpref.map fun v_tag => ∑ b : Bool,
            if bitAllowedFn x b = true ∧ nextWin d hd v_tag b = vt then
              evolvedFn x v_tag hh (xor (s.weval x tparW) (s.weval x (locW_i v_tag b)))
            else 0).sum % 2 ^ L)
    (D * D * (3 + H_b * ((p + 1) * (40 * (L + 1) ^ 2))) + 2 * (6 + H_b * (21 * L + 1)))
    (by
      intro s' acc v_tag vpref hs' _ ⟨hext, hacc, hev⟩
      have h0s' : s.Ext s' := CState.ext_trans h02 hext
      let initTab : (Fin (D * D + D * D) → ℕ) → Bool → BVec L := fun H par =>
        if par = false ∧ ∀ j : Fin (D * D), H ⟨D * D + j.val, by dsimp [D]; omega⟩ = 0 then
          dpW (fun j => H ⟨j.val, by dsimp [D]; omega⟩) v_tag
        else zeroBv
      have ha := mkInnerAux_spec d hd a0 p L (by omega) locW_i (D * D) le_rfl initTab
        (fun x H par =>
          if par = false ∧ ∀ j : Fin (D * D), H ⟨D * D + j.val, by dsimp [D]; omega⟩ = 0 then
            dpTab x (fun j => H ⟨j.val, by dsimp [D]; omega⟩) v_tag
          else 0)
        s' hs'
        (fun v b => lt_of_lt_of_le (hloc v b) (CState.ext_nw h0s'))
        (fun H par j => by
          dsimp only [initTab]; split_ifs
          · exact lt_of_lt_of_le (hdp _ v_tag j) (CState.ext_nw h0s')
          · exact lt_of_lt_of_le (hzero_s2 j) (CState.ext_nw hext))
        (fun x hx H par => by
          dsimp only [initTab]; split_ifs
          · rw [bvVal_ext h0s' x hx _ (hdp _ v_tag), hdp_ev x hx _ v_tag]
          · rw [bvVal_ext hext x hx zeroBv hzero_s2, hzero_ev x hx]; simp)
      set sa := (mkInnerAux d hd a0 L locW_i (D * D) le_rfl initTab s').1
      set evTab := (mkInnerAux d hd a0 L locW_i (D * D) le_rfl initTab s').2
      have h2a : s2.Ext sa := CState.ext_trans hext ha.1
      have hbfold := foldl_cstate_spec ([false, true] : List Bool)
        (fun (st2 : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) (b : Bool) =>
          let (sb, allowW) := mkAllowedW st2.1 b
          let (sc, needParW) := mkXor sb tparW (locW_i v_tag b)
          let v_tag' := nextWin d hd v_tag b
          (allHists (D * D) a0).foldl (fun (st3 : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) h' =>
            let (sd, rawVal) := mkBvIte L st3.1 needParW (evTab h' true) (evTab h' false)
            let (se, gatedVal) := mkBvIte L sd allowW rawVal zeroBv
            let (sf, sumVal) := mkBvAdd se (st3.2 h' v_tag') gatedVal
            (sf, fun hh vt => if hh = h' ∧ vt = v_tag' then sumVal else st3.2 hh vt)
          ) (sc, st2.2))
        (fun s'' acc'' bpref => sa.Ext s'' ∧ (∀ hh vt j, acc'' hh vt j < s''.nw) ∧
          ∀ x : List Bool, x.length = n_in → ∀ hh ∈ allHists (D * D) a0, ∀ vt : Fin D,
            bvVal s'' x (acc'' hh vt) =
              ((vpref.map fun vt0 => ∑ b : Bool,
                  if bitAllowedFn x b = true ∧ nextWin d hd vt0 b = vt then
                    evolvedFn x vt0 hh (xor (s.weval x tparW) (s.weval x (locW_i vt0 b)))
                  else 0).sum +
                (bpref.map fun b =>
                  if bitAllowedFn x b = true ∧ nextWin d hd v_tag b = vt then
                    evolvedFn x v_tag hh (xor (s.weval x tparW) (s.weval x (locW_i v_tag b)))
                  else 0).sum) % 2 ^ L)
        (6 + H_b * (21 * L + 1))
        (by
          intro s'' acc'' b bpref hs'' _ ⟨hext_a, hacc'', hev''⟩
          have h2s'' : s2.Ext s'' := CState.ext_trans h2a hext_a
          have hb' := hAllow_spec s'' hs'' h2s'' b
          set sb := (mkAllowedW s'' b).1; set allowW := (mkAllowedW s'' b).2
          have h0b : s.Ext sb := CState.ext_trans h02 (CState.ext_trans h2s'' hb'.1)
          have hc' := mkXor_spec sb hb'.2.1 tparW (locW_i v_tag b)
            (lt_of_lt_of_le htpar (CState.ext_nw h0b))
            (lt_of_lt_of_le (hloc v_tag b) (CState.ext_nw h0b))
          set sc := (mkXor sb tparW (locW_i v_tag b)).1
          set needParW := (mkXor sb tparW (locW_i v_tag b)).2
          have hs''c : s''.Ext sc := CState.ext_trans hb'.1 hc'.1
          let v_tag' := nextWin d hd v_tag b
          have hhfold := foldl_cstate_nodup_spec (allHists (D * D) a0) (nodup_allHists _ _)
            (fun (st3 : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) h' =>
              let (sd, rawVal) := mkBvIte L st3.1 needParW (evTab h' true) (evTab h' false)
              let (se, gatedVal) := mkBvIte L sd allowW rawVal zeroBv
              let (sf, sumVal) := mkBvAdd se (st3.2 h' v_tag') gatedVal
              (sf, fun hh vt => if hh = h' ∧ vt = v_tag' then sumVal else st3.2 hh vt))
            (fun s3 acc3 hpref => sc.Ext s3 ∧ (∀ hh vt j, acc3 hh vt j < s3.nw) ∧
              ∀ x : List Bool, x.length = n_in → ∀ hh ∈ allHists (D * D) a0, ∀ vt : Fin D,
                bvVal s3 x (acc3 hh vt) =
                  ((vpref.map fun vt0 => ∑ b0 : Bool,
                      if bitAllowedFn x b0 = true ∧ nextWin d hd vt0 b0 = vt then
                        evolvedFn x vt0 hh (xor (s.weval x tparW) (s.weval x (locW_i vt0 b0)))
                      else 0).sum +
                    (bpref.map fun b0 =>
                      if bitAllowedFn x b0 = true ∧ nextWin d hd v_tag b0 = vt then
                        evolvedFn x v_tag hh (xor (s.weval x tparW) (s.weval x (locW_i v_tag b0)))
                      else 0).sum +
                    if hh ∈ hpref ∧ bitAllowedFn x b = true ∧ v_tag' = vt then
                      evolvedFn x v_tag hh (xor (s.weval x tparW) (s.weval x (locW_i v_tag b)))
                    else 0) % 2 ^ L)
            (21 * L + 1)
            (by
              intro s3 acc3 h' hpref hs3 _ hnotin ⟨hext_c, hacc3, hev3⟩
              have ha3 : sa.Ext s3 := CState.ext_trans hext_a (CState.ext_trans hs''c hext_c)
              have h23 : s2.Ext s3 := CState.ext_trans h2a ha3
              have hd1 := mkBvIte_spec L s3 hs3 needParW (evTab h' true) (evTab h' false)
                (lt_of_lt_of_le hc'.2.2.1 (CState.ext_nw hext_c))
                (fun j => lt_of_lt_of_le (ha.2.2.1 h' true j) (CState.ext_nw ha3))
                (fun j => lt_of_lt_of_le (ha.2.2.1 h' false j) (CState.ext_nw ha3))
              set sd := (mkBvIte L s3 needParW (evTab h' true) (evTab h' false)).1
              set rawVal := (mkBvIte L s3 needParW (evTab h' true) (evTab h' false)).2
              have hbd : sb.Ext sd := CState.ext_trans hc'.1 (CState.ext_trans hext_c hd1.1)
              have h2d : s2.Ext sd := CState.ext_trans h23 hd1.1
              have he1 := mkBvIte_spec L sd hd1.2.1 allowW rawVal zeroBv
                (lt_of_lt_of_le hb'.2.2.1 (CState.ext_nw hbd)) hd1.2.2.1
                (fun j => lt_of_lt_of_le (hzero_s2 j) (CState.ext_nw h2d))
              set se := (mkBvIte L sd allowW rawVal zeroBv).1
              set gatedVal := (mkBvIte L sd allowW rawVal zeroBv).2
              have h3e : s3.Ext se := CState.ext_trans hd1.1 he1.1
              have hf1 := mkBvAdd_spec se he1.2.1 (acc3 h' v_tag') gatedVal
                (fun j => lt_of_lt_of_le (hacc3 h' v_tag' j) (CState.ext_nw h3e)) he1.2.2.1
              set sf := (mkBvAdd se (acc3 h' v_tag') gatedVal).1
              set sumVal := (mkBvAdd se (acc3 h' v_tag') gatedVal).2
              have h3f : s3.Ext sf := CState.ext_trans h3e hf1.1
              refine ⟨h3f, hf1.2.1, ?_, CState.ext_trans hext_c h3f, ?_, ?_⟩
              · have := hd1.2.2.2.1; have := he1.2.2.2.1; have := hf1.2.2.2.1
                dsimp only [sd, se, sf, rawVal, gatedVal, sumVal] at *; omega
              · intro hh vt j; dsimp only; split_ifs
                · exact hf1.2.2.1 j
                · exact lt_of_lt_of_le (hacc3 hh vt j) (CState.ext_nw h3f)
              · intro x hx hh hhh vt
                dsimp only
                have hloc_ext : (fun v b' => s'.weval x (locW_i v b')) = (fun v b' => s.weval x (locW_i v b')) :=
                  funext fun v => funext fun b' => CState.ext_weval h0s' x hx _ (hloc v b')
                by_cases hmatch : hh = h' ∧ vt = v_tag'
                · rcases hmatch with ⟨rfl, rfl⟩
                  rw [ite_eq_left_iff.mpr (fun h => False.elim (h ⟨rfl, rfl⟩)),
                    hf1.2.2.2.2 x hx, bvVal_ext h3e x hx (acc3 hh v_tag') (hacc3 hh v_tag'),
                    hev3 x hx hh hhh v_tag', he1.2.2.2.2 x hx,
                    CState.ext_weval hbd x hx allowW hb'.2.2.1, hb'.2.2.2.2 x hx,
                    hd1.2.2.2.2 x hx, CState.ext_weval hext_c x hx needParW hc'.2.2.1,
                    hc'.2.2.2.2 x hx, CState.ext_weval h0b x hx tparW htpar,
                    CState.ext_weval h0b x hx (locW_i v_tag b) (hloc v_tag b),
                    bvVal_ext ha3 x hx (evTab hh true) (ha.2.2.1 hh true),
                    bvVal_ext ha3 x hx (evTab hh false) (ha.2.2.1 hh false),
                    ha.2.2.2.2 x hx hh true, ha.2.2.2.2 x hx hh false,
                    bvVal_ext h2d x hx zeroBv hzero_s2, hzero_ev x hx, hloc_ext]
                  simp only [hnotin, false_and, ↓reduceIte, add_zero, List.mem_append, List.mem_singleton, or_true, true_and]
                  cases hba : bitAllowedFn x b
                  · simp only [bitAllowedFn] at hba ⊢
                    rw [hba]; simp only [Bool.false_eq_true, false_and, ↓reduceIte, add_zero, Nat.mod_mod]
                  · simp only [bitAllowedFn] at hba ⊢
                    rw [hba]; simp only [↓reduceIte, true_and]
                    cases hxp : xor (s.weval x tparW) (s.weval x (locW_i v_tag b)) <;>
                      simp only [↓reduceIte, Bool.false_eq_true] <;>
                      rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]
                · rw [ite_eq_right_iff.mpr (fun h => False.elim (hmatch h)),
                    bvVal_ext h3f x hx (acc3 hh vt) (hacc3 hh vt), hev3 x hx hh hhh vt]
                  congr 1; congr 1
                  by_cases hhh' : hh = h'
                  · have hvt : v_tag' ≠ vt := fun h => hmatch ⟨hhh', h.symm⟩
                    simp [hvt]
                  · simp [hhh'])
            sc hc'.2.1 acc'' [] (fun _ _ h => nomatch h) ⟨CState.ext_refl sc,
              fun hh vt j => lt_of_lt_of_le (hacc'' hh vt j) (CState.ext_nw hs''c),
              fun x hx hh hhh vt => by
                rw [bvVal_ext hs''c x hx (acc'' hh vt) (hacc'' hh vt), hev'' x hx hh hhh vt]; simp⟩
          refine ⟨CState.ext_trans hs''c hhfold.1, hhfold.2.1, ?_, CState.ext_trans hext_a (CState.ext_trans hs''c hhfold.1),
            hhfold.2.2.2.2.1, ?_⟩
          · have h1 := hb'.2.2.2.1; have h2 := hc'.2.2.2.1; have h3 := hhfold.2.2.1
            have hmul : (allHists (D * D) a0).length * (21 * L + 1) ≤ H_b * (21 * L + 1) :=
              Nat.mul_le_mul_right _ hHlen
            dsimp only [sb, sc] at h1 h2 h3
            exact le_trans h3 (by omega)
          · intro x hx hh hhh vt
            have h := hhfold.2.2.2.2.2 x hx hh hhh vt
            simp only [List.nil_append, hhh, true_and] at h
            rw [h, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero, Nat.add_assoc])
        sa ha.2.1 acc [] ⟨CState.ext_refl sa,
          fun hh vt j => lt_of_lt_of_le (hacc hh vt j) (CState.ext_nw ha.1),
          fun x hx hh hhh vt => by
            rw [bvVal_ext ha.1 x hx (acc hh vt) (hacc hh vt), hev x hx hh hhh vt]; simp⟩
      refine ⟨CState.ext_trans ha.1 hbfold.1, hbfold.2.1, ?_, CState.ext_trans hext (CState.ext_trans ha.1 hbfold.1),
        hbfold.2.2.2.2.1, ?_⟩
      · have h1 := ha.2.2.2.1; have h2 := hbfold.2.2.1
        simp only [List.length_cons, List.length_nil] at h2
        dsimp only [sa, D, H_b] at h1 h2 ⊢
        exact le_trans h2 (by omega)
      · intro x hx hh hhh vt
        have h := hbfold.2.2.2.2.2 x hx hh hhh vt
        simp only [List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
        rw [h, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        congr 2; rw [Fintype.sum_bool, Nat.add_comm])
    s2 hc1.2.1 (fun _ _ => zeroBv) [] ⟨CState.ext_refl s2, fun _ _ j => hzero_s2 j,
      fun x hx hh _ vt => by rw [hzero_ev x hx]; simp⟩
  refine ⟨CState.ext_trans h02 hfold.1, hfold.2.1, hfold.2.2.2.2.1, ?_, ?_⟩
  · have h1 := hz.2.2.2.1; have h2 := hc0.2.2.2.1; have h3 := hc1.2.2.2.1; have h4 := hfold.2.2.1
    simp only [List.length_finRange] at h4
    dsimp only [s0', s1, s2] at h1 h2 h3 h4
    exact le_trans h4 (by omega)
  · intro x hx hh hhh vt
    have h := hfold.2.2.2.2.2 x hx hh hhh vt
    simp only [List.nil_append] at h
    rw [h, ← List.sum_toFinset _ (List.nodup_finRange D)]
    have huniv : (List.finRange D).toFinset = Finset.univ := by ext v; simp
    rw [huniv]; rfl

def mkRunResidues {n_in : ℕ} (p n d : ℕ) (hd : 0 < d) (a0 r0 L : ℕ)
    (locW : Fin n → Fin (2 ^ d) → Bool → ℕ) (yW : Fin n → ℕ)
    (prefW : ℕ → ℕ) (s0 : Fin (2 ^ d)) :
    (i : ℕ) → (i ≤ n) → CState n_in →
    CState n_in × ((Fin (2 ^ d * 2 ^ d) → ℕ) → Fin (2 ^ d) → BVec L)
  | 0, _, s =>
    let D := 2 ^ d
    let (s0', zeroBv) := mkBvConst s L 0
    (List.finRange D).foldl (fun (st : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) (u : Fin D) =>
      let (sa, umW) := mkUTagMatchW a0 n r0 d prefW u st.1
      (allHists (D * D) a0).foldl (fun (st2 : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) h =>
        let (sb, pcBv) := mkBvConst st2.1 L (pathCount D a0 s0 u h)
        let (sc, val) := mkBvIte L sb umW pcBv zeroBv
        (sc, fun hh vt => if hh = h ∧ vt = u then val else st2.2 hh vt)
      ) (sa, st.2)
    ) (s0', fun _ _ => zeroBv)
  | i + 1, hi, s =>
    let (s1, prev) := mkRunResidues p n d hd a0 r0 L locW yW prefW s0 i (by omega) s
    let ifin : Fin n := ⟨i, hi⟩
    let (s2, hpW) := mkHighParW p n d a0 ifin (locW ifin) prefW s0 s1
    let (s3, tparW) := mkXor s2 (yW ifin) hpW
    mkResidueStep p n d hd a0 r0 L (locW ifin) prefW s0 ifin tparW prev s3

lemma mkRunResidues_spec {n_in : ℕ} (p n d : ℕ) (hd : 0 < d) (hdn : d < n) (a0 r0 L : ℕ)
    (ha0 : a0 < p) (locW : Fin n → Fin (2 ^ d) → Bool → ℕ) (yW : Fin n → ℕ)
    (prefW : ℕ → ℕ) (s0 : Fin (2 ^ d))
    (i : ℕ) (hi : i ≤ n) (s : CState n_in) (hs : s.Valid)
    (hloc : ∀ j v b, locW j v b < s.nw)
    (hy : ∀ j, yW j < s.nw)
    (hpref : ∀ pos < p * n, prefW pos < s.nw) :
    let D := 2 ^ d
    let H_b := (p + D ^ 3).choose p
    let initCost := 2 + D * (1 + d * 8 + H_b * (2 + 4 * L))
    let stepCost := (2 + p * (2 * (1 + D * (2 * d + 5)) + 9)) + 5 +
      (4 + D * (D * D * (3 + H_b * ((p + 1) * (40 * (L + 1) ^ 2))) + 2 * (6 + H_b * (21 * L + 1))))
    let res := mkRunResidues p n d hd a0 r0 L locW yW prefW s0 i hi s
    s.Ext res.1 ∧ res.1.Valid ∧ (∀ hh vt j, res.2 hh vt j < res.1.nw) ∧
    res.1.gates.length ≤ s.gates.length + initCost + i * stepCost ∧
    ∀ x : List Bool, x.length = n_in → ∀ hh ∈ allHists (D * D) a0, ∀ vt : Fin D,
      bvVal res.1 x (res.2 hh vt) =
        dpRunResidues p n d hd a0 r0 (fun j v b => s.weval x (locW j v b))
          (fun j => s.weval x (yW j)) (fun pos => s.weval x (prefW pos)) s0 i hi hh vt % 2 ^ L := by
  intro D H_b initCost stepCost
  have hHlen : (allHists (D * D) a0).length ≤ H_b := by
    have h := allHists_length_le_bound d a0 p 0 hd (by omega) (by omega)
    rw [zero_add] at h; exact h
  induction i generalizing s with
  | zero =>
    dsimp only [mkRunResidues, dpRunResidues]
    have hz := mkBvConst_spec s hs L 0
    set s0' := (mkBvConst s L 0).1; set zeroBv := (mkBvConst s L 0).2
    have hfold := foldl_cstate_spec (List.finRange D)
      (fun (st : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) (u : Fin D) =>
        let (sa, umW) := mkUTagMatchW a0 n r0 d prefW u st.1
        (allHists (D * D) a0).foldl (fun (st2 : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) h =>
          let (sb, pcBv) := mkBvConst st2.1 L (pathCount D a0 s0 u h)
          let (sc, val) := mkBvIte L sb umW pcBv zeroBv
          (sc, fun hh vt => if hh = h ∧ vt = u then val else st2.2 hh vt)
        ) (sa, st.2))
      (fun s' acc upref => s0'.Ext s' ∧ (∀ hh vt j, acc hh vt j < s'.nw) ∧
        ∀ x : List Bool, x.length = n_in → ∀ hh ∈ allHists (D * D) a0, ∀ vt ∈ upref,
          bvVal s' x (acc hh vt) =
            (if uTagMatch a0 n r0 d (fun pos => s.weval x (prefW pos)) vt = true then pathCount D a0 s0 vt hh else 0) % 2 ^ L)
      (1 + d * 8 + H_b * (2 + 4 * L))
      (by
        intro s' acc u upref hs' _ ⟨hext, hacc, hev⟩
        have h0s' : s.Ext s' := CState.ext_trans hz.1 hext
        have ha := mkUTagMatchW_spec a0 n r0 d prefW u s' hs' (fun t ht _ => by
          have hpos : a0 * n + t < p * n := by
            have : a0 * n + t < (a0 + 1) * n := by rw [Nat.add_mul, one_mul]; omega
            exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
          exact lt_of_lt_of_le (hpref _ hpos) (CState.ext_nw h0s'))
        set sa := (mkUTagMatchW a0 n r0 d prefW u s').1; set umW := (mkUTagMatchW a0 n r0 d prefW u s').2
        have hhfold := foldl_cstate_spec (allHists (D * D) a0)
          (fun (st2 : CState n_in × ((Fin (D * D) → ℕ) → Fin D → BVec L)) h =>
            let (sb, pcBv) := mkBvConst st2.1 L (pathCount D a0 s0 u h)
            let (sc, val) := mkBvIte L sb umW pcBv zeroBv
            (sc, fun hh vt => if hh = h ∧ vt = u then val else st2.2 hh vt))
          (fun s2 acc2 hpref' => sa.Ext s2 ∧ (∀ hh vt j, acc2 hh vt j < s2.nw) ∧
            ∀ x : List Bool, x.length = n_in → ∀ hh ∈ allHists (D * D) a0, ∀ vt : Fin D,
              (vt ∈ upref ∨ (vt = u ∧ hh ∈ hpref')) →
                bvVal s2 x (acc2 hh vt) =
                  (if uTagMatch a0 n r0 d (fun pos => s.weval x (prefW pos)) vt = true then pathCount D a0 s0 vt hh else 0) % 2 ^ L)
          (2 + 4 * L)
          (by
            intro s2 acc2 h hpref' hs2 _ ⟨hext_a, hacc2, hev2⟩
            have hb := mkBvConst_spec s2 hs2 L (pathCount D a0 s0 u h)
            set sb := (mkBvConst s2 L (pathCount D a0 s0 u h)).1; set pcBv := (mkBvConst s2 L (pathCount D a0 s0 u h)).2
            have hab : sa.Ext sb := CState.ext_trans hext_a hb.1
            have h0'b : s0'.Ext sb := CState.ext_trans hext (CState.ext_trans ha.1 hab)
            have hc := mkBvIte_spec L sb hb.2.1 umW pcBv zeroBv
              (lt_of_lt_of_le ha.2.2.1 (CState.ext_nw hab)) hb.2.2.1
              (fun j => lt_of_lt_of_le (hz.2.2.1 j) (CState.ext_nw h0'b))
            set sc := (mkBvIte L sb umW pcBv zeroBv).1; set val := (mkBvIte L sb umW pcBv zeroBv).2
            have h2c : s2.Ext sc := CState.ext_trans hb.1 hc.1
            refine ⟨h2c, hc.2.1,
              by have := hb.2.2.2.1; have := hc.2.2.2.1; dsimp only [sb, sc, pcBv, val] at *; omega,
              CState.ext_trans hext_a h2c, ?_, ?_⟩
            · intro hh vt j; dsimp only; split_ifs
              · exact hc.2.2.1 j
              · exact lt_of_lt_of_le (hacc2 hh vt j) (CState.ext_nw h2c)
            · intro x hx hh hhh vt hmem
              dsimp only
              by_cases hmatch : hh = h ∧ vt = u
              · rcases hmatch with ⟨rfl, rfl⟩
                rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' ⟨rfl, rfl⟩)),
                  hc.2.2.2.2 x hx, CState.ext_weval hab x hx umW ha.2.2.1, ha.2.2.2.2 x hx,
                  hb.2.2.2.2 x hx, bvVal_ext h0'b x hx zeroBv hz.2.2.1, hz.2.2.2.2 x hx]
                have hpref_ext : uTagMatch a0 n r0 d (fun pos => s'.weval x (prefW pos)) vt =
                    uTagMatch a0 n r0 d (fun pos => s.weval x (prefW pos)) vt := by
                  apply Bool.eq_iff_iff.mpr
                  simp only [uTagMatch, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
                  constructor <;> intro H t ht <;>
                    (by_cases hlt : t < r0
                     · exact Or.inl hlt
                     · have hpos : a0 * n + t < p * n := by
                         have : a0 * n + t < (a0 + 1) * n := by rw [Nat.add_mul, one_mul]; omega
                         exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
                       have := H t ht
                       rw [CState.ext_weval h0s' x hx _ (hpref _ hpos)] at *
                       exact this)
                rw [hpref_ext]
                cases uTagMatch a0 n r0 d (fun pos => s.weval x (prefW pos)) vt <;> simp
              · rw [ite_eq_right_iff.mpr (fun h' => False.elim (hmatch h')),
                  bvVal_ext h2c x hx (acc2 hh vt) (hacc2 hh vt)]
                apply hev2 x hx hh hhh vt
                rcases hmem with hmem | ⟨rfl, hmem⟩
                · exact Or.inl hmem
                · simp only [List.mem_append, List.mem_singleton] at hmem
                  rcases hmem with hmem | rfl
                  · exact Or.inr ⟨rfl, hmem⟩
                  · exact False.elim (hmatch ⟨rfl, rfl⟩))
          sa ha.2.1 acc [] ⟨CState.ext_refl sa,
            fun hh vt j => lt_of_lt_of_le (hacc hh vt j) (CState.ext_nw ha.1),
            fun x hx hh hhh vt hmem => by
              rcases hmem with hmem | ⟨_, hmem⟩
              · rw [bvVal_ext ha.1 x hx (acc hh vt) (hacc hh vt)]; exact hev x hx hh hhh vt hmem
              · exact nomatch hmem⟩
        refine ⟨CState.ext_trans ha.1 hhfold.1, hhfold.2.1, ?_, CState.ext_trans hext (CState.ext_trans ha.1 hhfold.1),
          hhfold.2.2.2.2.1, ?_⟩
        · have := ha.2.2.2.1; have := hhfold.2.2.1
          have hmul : (allHists (D * D) a0).length * (2 + 4 * L) ≤ H_b * (2 + 4 * L) :=
            Nat.mul_le_mul_right _ hHlen
          dsimp only [sa, umW] at *; omega
        · intro x hx hh hhh vt hvt
          simp only [List.mem_append, List.mem_singleton] at hvt
          apply hhfold.2.2.2.2.2 x hx hh hhh vt
          rcases hvt with hvt | rfl
          · exact Or.inl hvt
          · exact Or.inr ⟨rfl, by simp [hhh]⟩)
      s0' hz.2.1 (fun _ _ => zeroBv) [] ⟨CState.ext_refl s0', fun _ _ j => hz.2.2.1 j,
        fun _ _ _ _ _ h => nomatch h⟩
    refine ⟨CState.ext_trans hz.1 hfold.1, hfold.2.1, hfold.2.2.2.2.1, ?_, ?_⟩
    · have := hz.2.2.2.1; have := hfold.2.2.1
      simp only [List.length_finRange] at this; dsimp only [s0', zeroBv, initCost, D, H_b] at *; omega
    · intro x hx hh hhh vt
      exact hfold.2.2.2.2.2 x hx hh hhh vt (by simp)
  | succ i ih =>
    dsimp only [mkRunResidues, dpRunResidues]
    have h1 := ih (by omega) s hs hloc hy hpref
    set s1 := (mkRunResidues p n d hd a0 r0 L locW yW prefW s0 i (by omega) s).1
    set prev := (mkRunResidues p n d hd a0 r0 L locW yW prefW s0 i (by omega) s).2
    let ifin : Fin n := ⟨i, hi⟩
    have h2 := mkHighParW_spec p n d a0 ifin (locW ifin) prefW s0 s1 h1.2.1
      (fun v b => lt_of_lt_of_le (hloc ifin v b) (CState.ext_nw h1.1))
      (fun pos hpos => lt_of_lt_of_le (hpref pos hpos) (CState.ext_nw h1.1))
    set s2 := (mkHighParW p n d a0 ifin (locW ifin) prefW s0 s1).1
    set hpW := (mkHighParW p n d a0 ifin (locW ifin) prefW s0 s1).2
    have h02 : s.Ext s2 := CState.ext_trans h1.1 h2.1
    have h3 := mkXor_spec s2 h2.2.1 (yW ifin) hpW (lt_of_lt_of_le (hy ifin) (CState.ext_nw h02)) h2.2.2.1
    set s3 := (mkXor s2 (yW ifin) hpW).1; set tparW := (mkXor s2 (yW ifin) hpW).2
    have h13 : s1.Ext s3 := CState.ext_trans h2.1 h3.1
    have h03 : s.Ext s3 := CState.ext_trans h1.1 h13
    have h4 := mkResidueStep_spec p n d hd hdn a0 r0 L ha0 (locW ifin) prefW s0 ifin tparW prev
      (fun x hh vt =>
        if hh ∈ allHists (D * D) a0 then
          dpRunResidues p n d hd a0 r0 (fun j v b => s.weval x (locW j v b))
            (fun j => s.weval x (yW j)) (fun pos => s.weval x (prefW pos)) s0 i (by omega) hh vt
        else bvVal s1 x (prev hh vt))
      s3 h3.2.1
      (fun v b => lt_of_lt_of_le (hloc ifin v b) (CState.ext_nw h03))
      (fun pos hpos => lt_of_lt_of_le (hpref pos hpos) (CState.ext_nw h03))
      h3.2.2.1
      (fun hh vt j => lt_of_lt_of_le (h1.2.2.1 hh vt j) (CState.ext_nw h13))
      (fun x hx hh vt => by
        rw [bvVal_ext h13 x hx (prev hh vt) (h1.2.2.1 hh vt)]
        split_ifs with hmem
        · exact h1.2.2.2.2 x hx hh hmem vt
        · exact (Nat.mod_eq_of_lt (bvVal_lt s1 x (prev hh vt))).symm)
    refine ⟨CState.ext_trans h03 h4.1, h4.2.1, h4.2.2.1, ?_, ?_⟩
    · have := h1.2.2.2.1; have := h2.2.2.2.1; have := h3.2.2.2.1; have := h4.2.2.2.1
      dsimp only [s1, s2, s3, prev, hpW, tparW, ifin, stepCost, D, H_b] at *
      rw [Nat.add_mul, one_mul]; omega
    · intro x hx hh hhh vt
      rw [h4.2.2.2.2 x hx hh hhh vt]
      have hloc3 : (fun v b => s3.weval x (locW ifin v b)) = (fun v b => s.weval x (locW ifin v b)) :=
        funext fun v => funext fun b => CState.ext_weval h03 x hx _ (hloc ifin v b)
      have hpref1 : ∀ pos < p * n, s1.weval x (prefW pos) = s.weval x (prefW pos) :=
        fun pos hpos => CState.ext_weval h1.1 x hx _ (hpref pos hpos)
      have hpref3 : ∀ pos < p * n, s3.weval x (prefW pos) = s.weval x (prefW pos) :=
        fun pos hpos => CState.ext_weval h03 x hx _ (hpref pos hpos)
      have htpar_ev : s3.weval x tparW = xor (s.weval x (yW ifin))
          (highPar p n d a0 (fun j v b => s.weval x (locW j v b)) (fun pos => s.weval x (prefW pos)) s0 ifin) := by
        rw [h3.2.2.2.2 x hx, CState.ext_weval h02 x hx (yW ifin) (hy ifin), h2.2.2.2.2 x hx]
        congr 1
        unfold highPar
        have hcongr : ∀ (l : List (Fin p)) (acc : Bool),
            l.foldl (fun acc (a : Fin p) =>
              if a0 < a.val then xor acc (s1.weval x (locW ifin
                (highWin (p * n) d (fun pos => s1.weval x (prefW pos)) s0 (a.val * n + ifin.val))
                (highBit (p * n) d (fun pos => s1.weval x (prefW pos)) s0 (a.val * n + ifin.val + d))))
              else acc) acc =
            l.foldl (fun acc (a : Fin p) =>
              if a0 < a.val then xor acc (s.weval x (locW ifin
                (highWin (p * n) d (fun pos => s.weval x (prefW pos)) s0 (a.val * n + ifin.val))
                (highBit (p * n) d (fun pos => s.weval x (prefW pos)) s0 (a.val * n + ifin.val + d))))
              else acc) acc := by
          intro l; induction l with
          | nil => intro _; rfl
          | cons a t iht =>
            intro acc; simp only [List.foldl_cons]
            by_cases hgt : a0 < a.val
            · rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' hgt)), ite_eq_left_iff.mpr (fun h' => False.elim (h' hgt))]
              have hhb_eq : ∀ pos, highBit (p * n) d (fun u => s1.weval x (prefW u)) s0 pos =
                  highBit (p * n) d (fun u => s.weval x (prefW u)) s0 pos := by
                intro pos; dsimp only [highBit]; split_ifs with hlt
                · exact hpref1 pos hlt
                · rfl
              have hhw_eq : highWin (p * n) d (fun u => s1.weval x (prefW u)) s0 (a.val * n + ifin.val) =
                  highWin (p * n) d (fun u => s.weval x (prefW u)) s0 (a.val * n + ifin.val) := by
                apply Fin.ext; dsimp only [highWin]; apply Finset.sum_congr rfl; intro t _; rw [hhb_eq]
              rw [hhw_eq, hhb_eq, CState.ext_weval h1.1 x hx _ (hloc ifin _ _)]
              exact iht _
            · rw [ite_eq_right_iff.mpr (fun h' => False.elim (hgt h')), ite_eq_right_iff.mpr (fun h' => False.elim (hgt h'))]
              exact iht _
        exact hcongr (List.finRange p) false
      rw [hloc3, htpar_ev]
      apply congrArg (· % 2 ^ L)
      unfold dpResidueStep
      have hwt_eq : wTagOf p n d a0 (fun pos => s3.weval x (prefW pos)) s0 =
          wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0 := by
        dsimp only [wTagOf]; split_ifs with hlt
        · apply Fin.ext; dsimp only [highWin]; apply Finset.sum_congr rfl; intro t _
          dsimp only [highBit]
          have hpos : (a0 + 1) * n + t.val < p * n := by
            have : (a0 + 1) * n + t.val < (a0 + 2) * n := by rw [Nat.add_mul]; nlinarith [t.isLt]
            exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
          simp only [hpos, ↓reduceIte, hpref3 _ hpos]
        · rfl
      have hinner_congr : ∀ (v_tag : Fin D) (p_ev : Bool),
          dpInnerAux d hd a0 (fun v b => s.weval x (locW ifin v b)) (D * D) le_rfl
            (fun H par => if par = false ∧ ∀ j : Fin (D * D), H ⟨D * D + j.val, by dsimp [D]; omega⟩ = 0 then
              (if (fun j : Fin (D * D) => H ⟨j.val, by dsimp [D]; omega⟩) ∈ allHists (D * D) a0 then
                dpRunResidues p n d hd a0 r0 (fun j v b => s.weval x (locW j v b))
                  (fun j => s.weval x (yW j)) (fun pos => s.weval x (prefW pos)) s0 i (by omega)
                  (fun j => H ⟨j.val, by dsimp [D]; omega⟩) v_tag
               else bvVal s1 x (prev (fun j => H ⟨j.val, by dsimp [D]; omega⟩) v_tag))
            else 0) hh p_ev =
          dpInnerAux d hd a0 (fun v b => s.weval x (locW ifin v b)) (D * D) le_rfl
            (fun H par => if par = false ∧ ∀ j : Fin (D * D), H ⟨D * D + j.val, by dsimp [D]; omega⟩ = 0 then
              dpRunResidues p n d hd a0 r0 (fun j v b => s.weval x (locW j v b))
                (fun j => s.weval x (yW j)) (fun pos => s.weval x (prefW pos)) s0 i (by omega)
                (fun j => H ⟨j.val, by dsimp [D]; omega⟩) v_tag
            else 0) hh p_ev := by
        intro v_tag p_ev
        have hstep_congr : ∀ (rem : ℕ) (hrem : rem ≤ D * D)
            (t1 t2 : (Fin (rem + D * D) → ℕ) → Bool → ℕ),
            (∀ H ∈ allHists (rem + D * D) a0, ∀ q, t1 H q = t2 H q) →
            dpInnerAux d hd a0 (fun v b => s.weval x (locW ifin v b)) rem hrem t1 hh p_ev =
            dpInnerAux d hd a0 (fun v b => s.weval x (locW ifin v b)) rem hrem t2 hh p_ev := by
          intro rem
          induction rem with
          | zero =>
            intro _ t1 t2 ht; dsimp only [dpInnerAux]
            apply ht
            rw [mem_allHists]; have hsum := (mem_allHists _ _ hh).mp hhh
            rw [← hsum]
            exact Finset.sum_equiv (finCongr (Nat.zero_add (D * D))) (fun _ => by simp) (fun _ _ => rfl)
          | succ rem ihr =>
            intro hrem t1 t2 ht; dsimp only [dpInnerAux]
            apply ihr (by omega)
            intro H _ q
            rw [dpBinStep_eq_sum, dpBinStep_eq_sum]
            apply Finset.sum_congr rfl; intro h' hh'
            rw [List.mem_toFinset] at hh'
            apply Finset.sum_congr rfl; intro c0 _
            rw [ht h' hh']
        apply hstep_congr (D * D) le_rfl
        intro H hH q
        split_ifs with hcond hmem
        · rfl
        · exfalso; apply hmem
          rw [mem_allHists] at hH ⊢
          rw [← hH, Fin.sum_univ_add]
          have hz2 : ∑ j : Fin (D * D), H (Fin.natAdd (D * D) j) = 0 := by
            apply Finset.sum_eq_zero; intro j _
            exact hcond.2 j
          rw [hz2, add_zero]; rfl
        · rfl
      apply Finset.sum_congr rfl; intro v_tag _
      apply Finset.sum_congr rfl; intro b _
      dsimp only
      have hba_eq : (if ifin.val + d < r0 then true
          else if ifin.val + d < n then decide (b = s3.weval x (prefW (a0 * n + ifin.val + d)))
          else decide (b = (wTagOf p n d a0 (fun pos => s3.weval x (prefW pos)) s0).val.testBit (ifin.val + d - n))) =
        (if ifin.val + d < r0 then true
          else if ifin.val + d < n then decide (b = s.weval x (prefW (a0 * n + ifin.val + d)))
          else decide (b = (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0).val.testBit (ifin.val + d - n))) := by
        split_ifs with h1' h2'
        · rfl
        · have hpos : a0 * n + ifin.val + d < p * n := by
            have : a0 * n + ifin.val + d < (a0 + 1) * n := by rw [Nat.add_mul, one_mul]; omega
            exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
          rw [hpref3 _ hpos]
        · rw [hwt_eq]
      dsimp only [ifin, D] at hba_eq hinner_congr ⊢
      simp only [hba_eq, hinner_congr]

def mkPrefixCount {n_in : ℕ} (p n d : ℕ) (hd : 0 < d) (m L : ℕ)
    (locW : Fin n → Fin (2 ^ d) → Bool → ℕ) (yW : Fin n → ℕ)
    (prefW : ℕ → ℕ) (s : CState n_in) : CState n_in × BVec L :=
  let a0 := m / n
  let r0 := m % n
  let D := 2 ^ d
  let (s0', zeroBv) := mkBvConst s L 0
  let (s1, w0) := mkConst s0' false
  let (s2, w1) := mkConst s1 true
  (List.finRange D).foldl (fun (st : CState n_in × BVec L) (s0 : Fin D) =>
    let (sa, smW) := mkS0MatchW m d prefW s0 st.1
    let (sb, finalDp) := mkRunResidues p n d hd a0 r0 L locW yW prefW s0 n le_rfl sa
    let wTagBits : BVec d := fun t =>
      if a0 + 1 < p then prefW ((a0 + 1) * n + t.val)
      else if s0.val.testBit t.val then w1 else w0
    let (sc, diagSum) := (allHists (D * D) a0).foldl (fun (st2 : CState n_in × BVec L) h =>
      if isDiagHist D h = true then
        let (sd, val) := mkBvMuxFinD st2.1 wTagBits (finalDp h)
        mkBvAdd sd st2.2 val
      else st2) (sb, zeroBv)
    let (se, gated) := mkBvIte L sc smW diagSum zeroBv
    mkBvAdd se st.2 gated) (s2, zeroBv)

lemma mkPrefixCount_spec {n_in : ℕ} (p n d : ℕ) (hp : 2 ≤ p) (hd : 0 < d) (hdn : d < n)
    (m L : ℕ) (hm : m < p * n)
    (locW : Fin n → Fin (2 ^ d) → Bool → ℕ) (yW : Fin n → ℕ)
    (prefW : ℕ → ℕ) (s : CState n_in) (hs : s.Valid)
    (hloc : ∀ j v b, locW j v b < s.nw)
    (hy : ∀ j, yW j < s.nw)
    (hpref : ∀ pos < p * n, prefW pos < s.nw) :
    let D := 2 ^ d
    let H_b := (p + D ^ 3).choose p
    let initCost := 2 + D * (1 + d * 8 + H_b * (2 + 4 * L))
    let stepCost := (2 + p * (2 * (1 + D * (2 * d + 5)) + 9)) + 5 +
      (4 + D * (D * D * (3 + H_b * ((p + 1) * (40 * (L + 1) ^ 2))) + 2 * (6 + H_b * (21 * L + 1))))
    let diagCost := H_b * (2 + D * (2 * d + 1 + 4 * L) + 13 * L + 1)
    let res := mkPrefixCount p n d hd m L locW yW prefW s
    s.Ext res.1 ∧ res.1.Valid ∧ (∀ j, res.2 j < res.1.nw) ∧
    res.1.gates.length ≤ s.gates.length + 4 + D * (1 + d * 8 + initCost + n * stepCost + diagCost + 4 * L + 13 * L + 1) ∧
    ∀ x : List Bool, x.length = n_in →
      bvVal res.1 x res.2 =
        dpPrefixCount p n d hd m (fun j v b => s.weval x (locW j v b))
          (fun j => s.weval x (yW j)) (fun pos => s.weval x (prefW pos)) % 2 ^ L := by
  intro D H_b initCost stepCost diagCost
  dsimp only [mkPrefixCount]
  set a0 := m / n
  set r0 := m % n
  have hn : 0 < n := by omega
  have ha0 : a0 < p := (Nat.div_lt_iff_lt_mul hn).mpr hm
  have hHlen : (allHists (D * D) a0).length ≤ H_b := by
    have h := allHists_length_le_bound d a0 p 0 hd (by omega) (by omega)
    rw [zero_add] at h; exact h
  have hz := mkBvConst_spec s hs L 0
  set s0' := (mkBvConst s L 0).1; set zeroBv := (mkBvConst s L 0).2
  have hc0 := mkConst_spec s0' hz.2.1 false
  set s1 := (mkConst s0' false).1; set w0 := (mkConst s0' false).2
  have hc1 := mkConst_spec s1 hc0.2.1 true
  set s2 := (mkConst s1 true).1; set w1 := (mkConst s1 true).2
  have h02 : s.Ext s2 := CState.ext_trans hz.1 (CState.ext_trans hc0.1 hc1.1)
  have hzero_s2 : ∀ j, zeroBv j < s2.nw := fun j => lt_of_lt_of_le (hz.2.2.1 j) (CState.ext_nw (CState.ext_trans hc0.1 hc1.1))
  have hzero_ev : ∀ x : List Bool, x.length = n_in → bvVal s2 x zeroBv = 0 := by
    intro x hx; rw [bvVal_ext (CState.ext_trans hc0.1 hc1.1) x hx zeroBv hz.2.2.1, hz.2.2.2.2 x hx]; simp
  have hfold := foldl_cstate_spec (List.finRange D)
    (fun (st : CState n_in × BVec L) (s0 : Fin D) =>
      let (sa, smW) := mkS0MatchW m d prefW s0 st.1
      let (sb, finalDp) := mkRunResidues p n d hd a0 r0 L locW yW prefW s0 n le_rfl sa
      let wTagBits : BVec d := fun t =>
        if a0 + 1 < p then prefW ((a0 + 1) * n + t.val)
        else if s0.val.testBit t.val then w1 else w0
      let (sc, diagSum) := (allHists (D * D) a0).foldl (fun (st2 : CState n_in × BVec L) h =>
        if isDiagHist D h = true then
          let (sd, val) := mkBvMuxFinD st2.1 wTagBits (finalDp h)
          mkBvAdd sd st2.2 val
        else st2) (sb, zeroBv)
      let (se, gated) := mkBvIte L sc smW diagSum zeroBv
      mkBvAdd se st.2 gated)
    (fun s' acc s0pref => s2.Ext s' ∧ (∀ j, acc j < s'.nw) ∧
      ∀ x : List Bool, x.length = n_in →
        bvVal s' x acc =
          (s0pref.map fun s0 =>
            if s0Match m d (fun pos => s.weval x (prefW pos)) s0 = true then
              ((allHists (D * D) a0).map fun h =>
                if isDiagHist D h = true then
                  dpRunResidues p n d hd a0 r0 (fun j v b => s.weval x (locW j v b))
                    (fun j => s.weval x (yW j)) (fun pos => s.weval x (prefW pos)) s0 n le_rfl h
                    (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0)
                else 0).sum
            else 0).sum % 2 ^ L)
    (1 + d * 8 + initCost + n * stepCost + diagCost + 4 * L + 13 * L + 1)
    (by
      intro s' acc s0 s0pref hs' _ ⟨hext, hacc, hev⟩
      have h0s' : s.Ext s' := CState.ext_trans h02 hext
      have ha := mkS0MatchW_spec m d prefW s0 s' hs' (fun t ht _ => by
        have hpos : t < p * n := lt_of_lt_of_le (lt_trans ht hdn) (Nat.le_mul_of_pos_left n (by omega))
        exact lt_of_lt_of_le (hpref t hpos) (CState.ext_nw h0s'))
      set sa := (mkS0MatchW m d prefW s0 s').1; set smW := (mkS0MatchW m d prefW s0 s').2
      have h0a : s.Ext sa := CState.ext_trans h0s' ha.1
      have hb := mkRunResidues_spec p n d hd hdn a0 r0 L ha0 locW yW prefW s0 n le_rfl sa ha.2.1
        (fun j v b => lt_of_lt_of_le (hloc j v b) (CState.ext_nw h0a))
        (fun j => lt_of_lt_of_le (hy j) (CState.ext_nw h0a))
        (fun pos hpos => lt_of_lt_of_le (hpref pos hpos) (CState.ext_nw h0a))
      set sb := (mkRunResidues p n d hd a0 r0 L locW yW prefW s0 n le_rfl sa).1
      set finalDp := (mkRunResidues p n d hd a0 r0 L locW yW prefW s0 n le_rfl sa).2
      have h2b : s2.Ext sb := CState.ext_trans hext (CState.ext_trans ha.1 hb.1)
      have h0b : s.Ext sb := CState.ext_trans h02 h2b
      let wTagBits : BVec d := fun t =>
        if a0 + 1 < p then prefW ((a0 + 1) * n + t.val)
        else if s0.val.testBit t.val then w1 else w0
      have hwTag_lt : ∀ t, wTagBits t < s2.nw := by
        intro t; dsimp only [wTagBits]; split_ifs with hlt
        · have hpos : (a0 + 1) * n + t.val < p * n := by
            have : (a0 + 1) * n + t.val < (a0 + 2) * n := by rw [Nat.add_mul]; nlinarith [t.isLt]
            exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
          exact lt_of_lt_of_le (hpref _ hpos) (CState.ext_nw h02)
        · exact hc1.2.2.1
        · exact lt_of_lt_of_le hc0.2.2.1 (CState.ext_nw hc1.1)
      have hwTag_val : ∀ x : List Bool, x.length = n_in →
          (⟨bvVal s2 x wTagBits, bvVal_lt s2 x wTagBits⟩ : Fin D) =
            wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0 := by
        intro x hx; apply Fin.ext; apply Nat.eq_of_testBit_eq; intro t
        by_cases ht : t < d
        · rw [show (⟨bvVal s2 x wTagBits, bvVal_lt s2 x wTagBits⟩ : Fin D).val = bvVal s2 x wTagBits from rfl,
            bvVal_testBit s2 x wTagBits ⟨t, ht⟩]
          dsimp only [wTagBits, wTagOf]
          split_ifs with hlt htb
          · have hpos : (a0 + 1) * n + t < p * n := by
              have : (a0 + 1) * n + t < (a0 + 2) * n := by rw [Nat.add_mul]; nlinarith
              exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
            rw [highWin_testBit (p * n) d _ s0 _ t ht, CState.ext_weval h02 x hx _ (hpref _ hpos)]
            dsimp only [highBit]; rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' hpos))]
          · rw [hc1.2.2.2.2 x hx]; exact htb.symm
          · rw [CState.ext_weval hc1.1 x hx w0 hc0.2.2.1, hc0.2.2.2.2 x hx]
            exact (Bool.eq_false_iff.mpr htb).symm
        · have h1 : (⟨bvVal s2 x wTagBits, bvVal_lt s2 x wTagBits⟩ : Fin D).val < 2 ^ t :=
            lt_of_lt_of_le (bvVal_lt s2 x wTagBits) (Nat.pow_le_pow_right (by omega) (by omega))
          have h2 : (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0).val < 2 ^ t :=
            lt_of_lt_of_le (Fin.isLt _) (Nat.pow_le_pow_right (by omega) (by omega))
          rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
      have hdiag := foldl_cstate_spec (allHists (D * D) a0)
        (fun (st2 : CState n_in × BVec L) h =>
          if isDiagHist D h = true then
            let (sd, val) := mkBvMuxFinD st2.1 wTagBits (finalDp h)
            mkBvAdd sd st2.2 val
          else st2)
        (fun s3 acc3 hpref => sb.Ext s3 ∧ (∀ j, acc3 j < s3.nw) ∧
          ∀ x : List Bool, x.length = n_in →
            bvVal s3 x acc3 =
              (hpref.map fun h =>
                if isDiagHist D h = true then
                  dpRunResidues p n d hd a0 r0 (fun j v b => sa.weval x (locW j v b))
                    (fun j => sa.weval x (yW j)) (fun pos => sa.weval x (prefW pos)) s0 n le_rfl h
                    (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0)
                else 0).sum % 2 ^ L)
        (2 + D * (2 * d + 1 + 4 * L) + 13 * L + 1)
        (by
          intro s3 acc3 h hpref hs3 hh_mem ⟨hext_b, hacc3, hev3⟩
          have h23 : s2.Ext s3 := CState.ext_trans h2b hext_b
          by_cases hd_h : isDiagHist D h = true
          · rw [ite_eq_left_iff.mpr (fun h' => False.elim (h' hd_h))]
            have hd1 := mkBvMuxFinD_spec s3 hs3 wTagBits (finalDp h)
              (fun t => lt_of_lt_of_le (hwTag_lt t) (CState.ext_nw h23))
              (fun vt j => lt_of_lt_of_le (hb.2.2.1 h vt j) (CState.ext_nw hext_b))
            set sd := (mkBvMuxFinD s3 wTagBits (finalDp h)).1
            set val := (mkBvMuxFinD s3 wTagBits (finalDp h)).2
            have he1 := mkBvAdd_spec sd hd1.2.1 acc3 val
              (fun j => lt_of_lt_of_le (hacc3 j) (CState.ext_nw hd1.1)) hd1.2.2.1
            refine ⟨CState.ext_trans hd1.1 he1.1, he1.2.1,
              by have h1 := hd1.2.2.2.1; have h2 := he1.2.2.2.1; dsimp only [sd, D] at h1 h2 ⊢; exact le_trans h2.le (by omega),
              CState.ext_trans hext_b (CState.ext_trans hd1.1 he1.1), he1.2.2.1, ?_⟩
            intro x hx
            rw [he1.2.2.2.2 x hx, bvVal_ext hd1.1 x hx acc3 hacc3, hev3 x hx, hd1.2.2.2.2 x hx]
            have hwt3 : (⟨bvVal s3 x wTagBits, bvVal_lt s3 x wTagBits⟩ : Fin D) =
                wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0 := by
              apply Fin.ext; dsimp only; rw [bvVal_ext h23 x hx wTagBits hwTag_lt]
              exact congrArg Fin.val (hwTag_val x hx)
            rw [hwt3, bvVal_ext hext_b x hx (finalDp h _) (hb.2.2.1 h _), hb.2.2.2.2 x hx h hh_mem _,
              List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero,
              ite_eq_left_iff.mpr (fun h' => False.elim (h' hd_h)),
              Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]
          · rw [ite_eq_right_iff.mpr (fun h' => False.elim (hd_h h'))]
            refine ⟨CState.ext_refl s3, hs3, by dsimp only; omega, hext_b, hacc3, ?_⟩
            intro x hx
            rw [hev3 x hx, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
              ite_eq_right_iff.mpr (fun h' => False.elim (hd_h h')), add_zero, add_zero])
        sb hb.2.1 zeroBv [] ⟨CState.ext_refl sb, fun j => lt_of_lt_of_le (hzero_s2 j) (CState.ext_nw h2b),
          fun x hx => by rw [bvVal_ext h2b x hx zeroBv hzero_s2, hzero_ev x hx]; simp⟩
      set sc := ((allHists (D * D) a0).foldl _ (sb, zeroBv)).1
      set diagSum := ((allHists (D * D) a0).foldl _ (sb, zeroBv)).2
      have hac : sa.Ext sc := CState.ext_trans hb.1 hdiag.1
      have h2c : s2.Ext sc := CState.ext_trans h2b hdiag.1
      have he1 := mkBvIte_spec L sc hdiag.2.1 smW diagSum zeroBv
        (lt_of_lt_of_le ha.2.2.1 (CState.ext_nw hac)) hdiag.2.2.2.2.1
        (fun j => lt_of_lt_of_le (hzero_s2 j) (CState.ext_nw h2c))
      set se := (mkBvIte L sc smW diagSum zeroBv).1; set gated := (mkBvIte L sc smW diagSum zeroBv).2
      have hs'e : s'.Ext se := CState.ext_trans ha.1 (CState.ext_trans hac he1.1)
      have hf1 := mkBvAdd_spec se he1.2.1 acc gated
        (fun j => lt_of_lt_of_le (hacc j) (CState.ext_nw hs'e)) he1.2.2.1
      refine ⟨CState.ext_trans hs'e hf1.1, hf1.2.1, ?_, CState.ext_trans hext (CState.ext_trans hs'e hf1.1), hf1.2.2.1, ?_⟩
      · have h1 := ha.2.2.2.1; have h2 := hb.2.2.2.1; have h3 := hdiag.2.2.1
        have h4 := he1.2.2.2.1; have h5 := hf1.2.2.2.1
        have hmul : (allHists (D * D) a0).length * (2 + D * (2 * d + 1 + 4 * L) + 13 * L + 1) ≤ diagCost :=
          Nat.mul_le_mul_right _ hHlen
        dsimp only [sa, sb, sc, se, D, H_b, initCost, stepCost, diagCost] at h1 h2 h3 h4 h5 hmul ⊢
        exact le_trans h5.le (by omega)
      · intro x hx
        rw [hf1.2.2.2.2 x hx, bvVal_ext hs'e x hx acc hacc, hev x hx,
          he1.2.2.2.2 x hx, CState.ext_weval hac x hx smW ha.2.2.1, ha.2.2.2.2 x hx,
          hdiag.2.2.2.2.2 x hx, bvVal_ext h2c x hx zeroBv hzero_s2, hzero_ev x hx]
        simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        have hs0_ext : s0Match m d (fun pos => s'.weval x (prefW pos)) s0 =
            s0Match m d (fun pos => s.weval x (prefW pos)) s0 := by
          apply Bool.eq_iff_iff.mpr
          simp only [s0Match, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
          constructor <;> intro H t ht <;>
            (by_cases hlt : t < m
             · exact Or.inl hlt
             · have hpos : t < p * n := lt_of_lt_of_le (lt_trans ht hdn) (Nat.le_mul_of_pos_left n (by omega))
               have := H t ht; rw [CState.ext_weval h0s' x hx _ (hpref t hpos)] at *; exact this)
        have hloc_a : (fun j v b => sa.weval x (locW j v b)) = (fun j v b => s.weval x (locW j v b)) :=
          funext fun j => funext fun v => funext fun b => CState.ext_weval h0a x hx _ (hloc j v b)
        have hy_a : (fun j => sa.weval x (yW j)) = (fun j => s.weval x (yW j)) :=
          funext fun j => CState.ext_weval h0a x hx _ (hy j)
        have hpref_a : ∀ h ∈ allHists (D * D) a0,
            dpRunResidues p n d hd a0 r0 (fun j v b => s.weval x (locW j v b))
              (fun j => s.weval x (yW j)) (fun pos => sa.weval x (prefW pos)) s0 n le_rfl h
              (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0) =
            dpRunResidues p n d hd a0 r0 (fun j v b => s.weval x (locW j v b))
              (fun j => s.weval x (yW j)) (fun pos => s.weval x (prefW pos)) s0 n le_rfl h
              (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0) := by
          intro h _

          have hcongr : ∀ (i' : ℕ) (hi' : i' ≤ n) (hh' : Fin (D * D) → ℕ) (vt' : Fin D),
              dpRunResidues p n d hd a0 r0 (fun j v b => s.weval x (locW j v b))
                (fun j => s.weval x (yW j)) (fun pos => sa.weval x (prefW pos)) s0 i' hi' hh' vt' =
              dpRunResidues p n d hd a0 r0 (fun j v b => s.weval x (locW j v b))
                (fun j => s.weval x (yW j)) (fun pos => s.weval x (prefW pos)) s0 i' hi' hh' vt' := by
            intro i'
            induction i' with
            | zero =>
              intro _ hh' vt'; dsimp only [dpRunResidues]
              have hu : uTagMatch a0 n r0 d (fun pos => sa.weval x (prefW pos)) vt' =
                  uTagMatch a0 n r0 d (fun pos => s.weval x (prefW pos)) vt' := by
                apply Bool.eq_iff_iff.mpr
                simp only [uTagMatch, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
                constructor <;> intro H t ht <;>
                  (by_cases hlt : t < r0
                   · exact Or.inl hlt
                   · have hpos : a0 * n + t < p * n := by
                       have : a0 * n + t < (a0 + 1) * n := by rw [Nat.add_mul, one_mul]; omega
                       exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
                     have := H t ht; rw [CState.ext_weval h0a x hx _ (hpref _ hpos)] at *; exact this)
              rw [hu]
            | succ j ihj =>
              intro hj hh' vt'; dsimp only [dpRunResidues]
              have hprev_eq : dpRunResidues p n d hd a0 r0 (fun j' v b => s.weval x (locW j' v b))
                  (fun j' => s.weval x (yW j')) (fun pos => sa.weval x (prefW pos)) s0 j (by omega) =
                dpRunResidues p n d hd a0 r0 (fun j' v b => s.weval x (locW j' v b))
                  (fun j' => s.weval x (yW j')) (fun pos => s.weval x (prefW pos)) s0 j (by omega) :=
                funext fun h1 => funext fun v1 => ihj (by omega) h1 v1
              have hhb_a : ∀ pos, highBit (p * n) d (fun u => sa.weval x (prefW u)) s0 pos =
                  highBit (p * n) d (fun u => s.weval x (prefW u)) s0 pos := by
                intro pos; dsimp only [highBit]; split_ifs with hlt
                · exact CState.ext_weval h0a x hx _ (hpref pos hlt)
                · rfl
              have hhw_a : ∀ pos, highWin (p * n) d (fun u => sa.weval x (prefW u)) s0 pos =
                  highWin (p * n) d (fun u => s.weval x (prefW u)) s0 pos := by
                intro pos; apply Fin.ext; dsimp only [highWin]; apply Finset.sum_congr rfl; intro t _; rw [hhb_a]
              have hhp_a : highPar p n d a0 (fun j' v b => s.weval x (locW j' v b))
                  (fun pos => sa.weval x (prefW pos)) s0 ⟨j, hj⟩ =
                highPar p n d a0 (fun j' v b => s.weval x (locW j' v b))
                  (fun pos => s.weval x (prefW pos)) s0 ⟨j, hj⟩ := by
                unfold highPar; simp only [hhw_a, hhb_a]
              have hwt_a : wTagOf p n d a0 (fun pos => sa.weval x (prefW pos)) s0 =
                  wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0 := by
                unfold wTagOf; simp only [hhw_a]
              rw [hprev_eq, hhp_a]
              unfold dpResidueStep; dsimp only
              apply Finset.sum_congr rfl; intro v_tag _
              apply Finset.sum_congr rfl; intro b _
              have hba : (if j + d < r0 then true
                  else if j + d < n then decide (b = sa.weval x (prefW (a0 * n + j + d)))
                  else decide (b = (wTagOf p n d a0 (fun pos => sa.weval x (prefW pos)) s0).val.testBit (j + d - n))) =
                (if j + d < r0 then true
                  else if j + d < n then decide (b = s.weval x (prefW (a0 * n + j + d)))
                  else decide (b = (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0).val.testBit (j + d - n))) := by
                split_ifs with h1' h2'
                · rfl
                · have hpos : a0 * n + j + d < p * n := by
                    have : a0 * n + j + d < (a0 + 1) * n := by rw [Nat.add_mul, one_mul]; omega
                    exact lt_of_lt_of_le this (Nat.mul_le_mul_right n (by omega))
                  rw [CState.ext_weval h0a x hx _ (hpref _ hpos)]
                · rw [hwt_a]
              simp only [hba]
          exact hcongr n le_rfl h _
        rw [hs0_ext, hloc_a, hy_a]
        have hmap_eq : ((allHists (D * D) a0).map fun h =>
            if isDiagHist D h = true then
              dpRunResidues p n d hd a0 r0 (fun j v b => s.weval x (locW j v b))
                (fun j => s.weval x (yW j)) (fun pos => sa.weval x (prefW pos)) s0 n le_rfl h
                (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0)
            else 0) =
          ((allHists (D * D) a0).map fun h =>
            if isDiagHist D h = true then
              dpRunResidues p n d hd a0 r0 (fun j v b => s.weval x (locW j v b))
                (fun j => s.weval x (yW j)) (fun pos => s.weval x (prefW pos)) s0 n le_rfl h
                (wTagOf p n d a0 (fun pos => s.weval x (prefW pos)) s0)
            else 0) :=
          List.map_congr_left fun h hh => by split_ifs <;> [exact hpref_a h hh; rfl]
        rw [hmap_eq]
        cases s0Match m d (fun pos => s.weval x (prefW pos)) s0
        · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, Nat.mod_mod]
        · simp only [↓reduceIte, zero_add]
          rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod])
    s2 hc1.2.1 zeroBv [] ⟨CState.ext_refl s2, hzero_s2, fun x hx => by rw [hzero_ev x hx]; simp⟩
  refine ⟨CState.ext_trans h02 hfold.1, hfold.2.1, hfold.2.2.2.2.1, ?_, ?_⟩
  · have h1 := hz.2.2.2.1; have h2 := hc0.2.2.2.1; have h3 := hc1.2.2.2.1; have h4 := hfold.2.2.1
    simp only [List.length_finRange] at h4
    dsimp only [s0', s1, s2] at h1 h2 h3 h4
    exact le_trans h4 (by omega)
  · intro x hx
    have h := hfold.2.2.2.2.2 x hx
    simp only [List.nil_append] at h
    rw [h, ← List.sum_toFinset _ (List.nodup_finRange D)]
    have huniv : (List.finRange D).toFinset = Finset.univ := by ext v; simp
    rw [huniv]; rfl

def mkUnrankLoop {n_in : ℕ} (p n d : ℕ) (hd : 0 < d) (L : ℕ)
    (locW : Fin n → Fin (2 ^ d) → Bool → ℕ) (yW : Fin n → ℕ) :
    (m : ℕ) → CState n_in → BVec L → (ℕ → ℕ) → CState n_in × BVec L × (ℕ → ℕ)
  | 0, s, remBv, prefW => (s, remBv, prefW)
  | m + 1, s, remBv, prefW =>
    let (s0, w0) := mkConst s false
    let pref0W := Function.update prefW m w0
    let (s1, c0Bv) := mkPrefixCount p n d hd m L locW yW pref0W s0
    let (s2, isLtW) := mkBvLtAux L s1 remBv c0Bv
    let (s3, subBv) := mkBvSub s2 remBv c0Bv
    let (s4, remNext) := mkBvIte L s3 isLtW remBv subBv
    let (s5, bitW) := mkNot s4 isLtW
    mkUnrankLoop p n d hd L locW yW m s5 remNext (Function.update prefW m bitW)

lemma mkUnrankLoop_spec {n_in : ℕ} (p n d : ℕ) (hp : 2 ≤ p) (hd : 0 < d) (hdn : d < n)
    (locW : Fin n → Fin (2 ^ d) → Bool → ℕ) (yW : Fin n → ℕ)
    (m : ℕ) (hm : m ≤ p * n) (s : CState n_in) (hs : s.Valid)
    (remBv : BVec (p * n + 1)) (prefW : ℕ → ℕ)
    (hloc : ∀ j v b, locW j v b < s.nw)
    (hy : ∀ j, yW j < s.nw)
    (hrem : ∀ j, remBv j < s.nw)
    (hpref : ∀ pos < p * n, prefW pos < s.nw) :
    let k := p * n
    let L := k + 1
    let D := 2 ^ d
    let H_b := (p + D ^ 3).choose p
    let initCost := 2 + D * (1 + d * 8 + H_b * (2 + 4 * L))
    let stepCost := (2 + p * (2 * (1 + D * (2 * d + 5)) + 9)) + 5 +
      (4 + D * (D * D * (3 + H_b * ((p + 1) * (40 * (L + 1) ^ 2))) + 2 * (6 + H_b * (21 * L + 1))))
    let diagCost := H_b * (2 + D * (2 * d + 1 + 4 * L) + 13 * L + 1)
    let prefCost := 4 + D * (1 + d * 8 + initCost + n * stepCost + diagCost + 4 * L + 13 * L + 1)
    let res := mkUnrankLoop p n d hd L locW yW m s remBv prefW
    s.Ext res.1 ∧ res.1.Valid ∧ (∀ j, res.2.1 j < res.1.nw) ∧ (∀ pos < k, res.2.2 pos < res.1.nw) ∧
    res.1.gates.length ≤ s.gates.length + m * (prefCost + 28 * L + 4) ∧
    ∀ x : List Bool, x.length = n_in →
      let cntFn := fun m' pf => dpPrefixCount p n d hd m' (fun j v b => s.weval x (locW j v b))
        (fun j => s.weval x (yW j)) pf
      let ures := unrankLoop k cntFn m (bvVal s x remBv, fun pos => s.weval x (prefW pos))
      bvVal res.1 x res.2.1 = ures.1 ∧ ∀ pos < k, res.1.weval x (res.2.2 pos) = ures.2 pos := by
  intro k L D H_b initCost stepCost diagCost prefCost
  induction m generalizing s remBv prefW with
  | zero =>
    refine ⟨CState.ext_refl s, hs, hrem, hpref, by simp [mkUnrankLoop], ?_⟩
    intro x _; exact ⟨rfl, fun _ _ => rfl⟩
  | succ m ih =>
    dsimp only [mkUnrankLoop]
    have hc0 := mkConst_spec s hs false
    set s0 := (mkConst s false).1; set w0 := (mkConst s false).2
    let pref0W := Function.update prefW m w0
    have hpref0 : ∀ pos < k, pref0W pos < s0.nw := by
      intro pos hpos; dsimp only [pref0W]
      by_cases heq : pos = m
      · rw [heq, Function.update_self]; exact hc0.2.2.1
      · rw [Function.update_of_ne heq]; exact lt_of_lt_of_le (hpref pos hpos) (CState.ext_nw hc0.1)
    have h1 := mkPrefixCount_spec p n d hp hd hdn m L (by omega) locW yW pref0W s0 hc0.2.1
      (fun j v b => lt_of_lt_of_le (hloc j v b) (CState.ext_nw hc0.1))
      (fun j => lt_of_lt_of_le (hy j) (CState.ext_nw hc0.1)) hpref0
    set s1 := (mkPrefixCount p n d hd m L locW yW pref0W s0).1
    set c0Bv := (mkPrefixCount p n d hd m L locW yW pref0W s0).2
    have h01 : s.Ext s1 := CState.ext_trans hc0.1 h1.1
    have h2 := mkBvLt_spec L s1 h1.2.1 remBv c0Bv
      (fun j => lt_of_lt_of_le (hrem j) (CState.ext_nw h01)) h1.2.2.1
    set s2 := (mkBvLtAux L s1 remBv c0Bv).1; set isLtW := (mkBvLtAux L s1 remBv c0Bv).2
    have h02 : s.Ext s2 := CState.ext_trans h01 h2.1
    have h3 := mkBvSub_spec s2 h2.2.1 remBv c0Bv
      (fun j => lt_of_lt_of_le (hrem j) (CState.ext_nw h02))
      (fun j => lt_of_lt_of_le (h1.2.2.1 j) (CState.ext_nw h2.1))
    set s3 := (mkBvSub s2 remBv c0Bv).1; set subBv := (mkBvSub s2 remBv c0Bv).2
    have h03 : s.Ext s3 := CState.ext_trans h02 h3.1
    have h4 := mkBvIte_spec L s3 h3.2.1 isLtW remBv subBv
      (lt_of_lt_of_le h2.2.2.1 (CState.ext_nw h3.1))
      (fun j => lt_of_lt_of_le (hrem j) (CState.ext_nw h03)) h3.2.2.1
    set s4 := (mkBvIte L s3 isLtW remBv subBv).1; set remNext := (mkBvIte L s3 isLtW remBv subBv).2
    have h24 : s2.Ext s4 := CState.ext_trans h3.1 h4.1
    have h5 := mkNot_spec s4 h4.2.1 isLtW (lt_of_lt_of_le h2.2.2.1 (CState.ext_nw h24))
    set s5 := (mkNot s4 isLtW).1; set bitW := (mkNot s4 isLtW).2
    have h05 : s.Ext s5 := CState.ext_trans h03 (CState.ext_trans h4.1 h5.1)
    have hpref_next : ∀ pos < k, Function.update prefW m bitW pos < s5.nw := by
      intro pos hpos
      by_cases heq : pos = m
      · rw [heq, Function.update_self]; exact h5.2.2.1
      · rw [Function.update_of_ne heq]; exact lt_of_lt_of_le (hpref pos hpos) (CState.ext_nw h05)
    have hrec := ih (by omega) s5 h5.2.1 remNext (Function.update prefW m bitW)
      (fun j v b => lt_of_lt_of_le (hloc j v b) (CState.ext_nw h05))
      (fun j => lt_of_lt_of_le (hy j) (CState.ext_nw h05))
      (fun j => lt_of_lt_of_le (h4.2.2.1 j) (CState.ext_nw h5.1)) hpref_next
    refine ⟨CState.ext_trans h05 hrec.1, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1, ?_, ?_⟩
    · have ha := hc0.2.2.2.1; have hb := h1.2.2.2.1; have hc := h2.2.2.2.1
      have hd' := h3.2.2.2.1; have he := h4.2.2.2.1; have hf := h5.2.2.2.1; have hg := hrec.2.2.2.2.1
      have hmul : (m + 1) * (prefCost + 28 * L + 4) = m * (prefCost + 28 * L + 4) + (prefCost + 28 * L + 4) := by
        rw [Nat.add_mul, one_mul]
      dsimp only [s0, s1, s2, s3, s4, s5, prefCost, diagCost, stepCost, initCost, D, H_b] at *
      exact le_trans hg (by omega)
    · intro x hx
      have hrec_ev := hrec.2.2.2.2.2 x hx

      have hc0_val : bvVal s1 x c0Bv = dpPrefixCount p n d hd m (fun j v b => s.weval x (locW j v b))
          (fun j => s.weval x (yW j)) (Function.update (fun pos => s.weval x (prefW pos)) m false) := by
        rw [h1.2.2.2.2 x hx]
        have hloc0 : (fun j v b => s0.weval x (locW j v b)) = (fun j v b => s.weval x (locW j v b)) :=
          funext fun j => funext fun v => funext fun b => CState.ext_weval hc0.1 x hx _ (hloc j v b)
        have hy0 : (fun j => s0.weval x (yW j)) = (fun j => s.weval x (yW j)) :=
          funext fun j => CState.ext_weval hc0.1 x hx _ (hy j)
        rw [hloc0, hy0]
        have hpf_eq : dpPrefixCount p n d hd m (fun j v b => s.weval x (locW j v b))
            (fun j => s.weval x (yW j)) (fun pos => s0.weval x (pref0W pos)) =
          dpPrefixCount p n d hd m (fun j v b => s.weval x (locW j v b))
            (fun j => s.weval x (yW j)) (Function.update (fun pos => s.weval x (prefW pos)) m false) := by
          rw [dpPrefixCount_spec p n d hp hd hdn m (by omega), dpPrefixCount_spec p n d hp hd hdn m (by omega)]
          congr 1; ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine and_congr_left fun _ => forall₃_congr fun pos _ hpos => ?_
          dsimp only [pref0W]
          by_cases heq : pos = m
          · rw [heq, Function.update_self, Function.update_self, hc0.2.2.2.2 x hx]
          · rw [Function.update_of_ne heq, Function.update_of_ne heq, CState.ext_weval hc0.1 x hx _ (hpref pos hpos)]
        rw [hpf_eq]
        apply Nat.mod_eq_of_lt
        rw [dpPrefixCount_spec p n d hp hd hdn m (by omega)]
        exact lt_of_le_of_lt
          (le_trans (Finset.card_le_univ _) (by simp [k]))
          (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self k))
      have hisLt_ev : s2.weval x isLtW = decide (bvVal s x remBv < dpPrefixCount p n d hd m
          (fun j v b => s.weval x (locW j v b)) (fun j => s.weval x (yW j))
          (Function.update (fun pos => s.weval x (prefW pos)) m false)) := by
        rw [h2.2.2.2.2 x hx, bvVal_ext h01 x hx remBv hrem, hc0_val]
      have hremNext_ev : bvVal s5 x remNext =
          if bvVal s x remBv < dpPrefixCount p n d hd m (fun j v b => s.weval x (locW j v b))
              (fun j => s.weval x (yW j)) (Function.update (fun pos => s.weval x (prefW pos)) m false) then
            bvVal s x remBv
          else bvVal s x remBv - dpPrefixCount p n d hd m (fun j v b => s.weval x (locW j v b))
              (fun j => s.weval x (yW j)) (Function.update (fun pos => s.weval x (prefW pos)) m false) := by
        rw [bvVal_ext h5.1 x hx remNext h4.2.2.1, h4.2.2.2.2 x hx,
          CState.ext_weval h3.1 x hx isLtW h2.2.2.1, hisLt_ev,
          bvVal_ext h03 x hx remBv hrem]
        by_cases hlt : bvVal s x remBv < dpPrefixCount p n d hd m (fun j v b => s.weval x (locW j v b))
            (fun j => s.weval x (yW j)) (Function.update (fun pos => s.weval x (prefW pos)) m false)
        · simp [hlt]
        · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [h3.2.2.2.2 x hx (by rw [bvVal_ext h02 x hx remBv hrem, bvVal_ext h2.1 x hx c0Bv h1.2.2.1, hc0_val]; omega),
            bvVal_ext h02 x hx remBv hrem, bvVal_ext h2.1 x hx c0Bv h1.2.2.1, hc0_val]
      have hpref5_ev : ∀ pos < k, s5.weval x (Function.update prefW m bitW pos) =
          Function.update (fun pos => s.weval x (prefW pos)) m
            (!(decide (bvVal s x remBv < dpPrefixCount p n d hd m (fun j v b => s.weval x (locW j v b))
              (fun j => s.weval x (yW j)) (Function.update (fun pos => s.weval x (prefW pos)) m false)))) pos := by
        intro pos hpos
        by_cases heq : pos = m
        · rw [heq, Function.update_self, Function.update_self, h5.2.2.2.2 x hx,
            CState.ext_weval h24 x hx isLtW h2.2.2.1, hisLt_ev]
        · rw [Function.update_of_ne heq, Function.update_of_ne heq, CState.ext_weval h05 x hx _ (hpref pos hpos)]

      have hunrank_congr : ∀ (m' : ℕ) (hm' : m' ≤ k) (r' : ℕ) (pf1 pf2 : ℕ → Bool),
          (∀ pos < k, pf1 pos = pf2 pos) →
          let c1 := fun mm pf => dpPrefixCount p n d hd mm (fun j v b => s5.weval x (locW j v b)) (fun j => s5.weval x (yW j)) pf
          let c2 := fun mm pf => dpPrefixCount p n d hd mm (fun j v b => s.weval x (locW j v b)) (fun j => s.weval x (yW j)) pf
          (unrankLoop k c1 m' (r', pf1)).1 = (unrankLoop k c2 m' (r', pf2)).1 ∧
          ∀ pos < k, (unrankLoop k c1 m' (r', pf1)).2 pos = (unrankLoop k c2 m' (r', pf2)).2 pos := by
        intro m'
        induction m' with
        | zero => intro _ r' pf1 pf2 hpf; exact ⟨rfl, hpf⟩
        | succ m' ihm =>
          intro hm' r' pf1 pf2 hpf
          dsimp only [unrankLoop]
          have hloc5 : (fun j v b => s5.weval x (locW j v b)) = (fun j v b => s.weval x (locW j v b)) :=
            funext fun j => funext fun v => funext fun b => CState.ext_weval h05 x hx _ (hloc j v b)
          have hy5 : (fun j => s5.weval x (yW j)) = (fun j => s.weval x (yW j)) :=
            funext fun j => CState.ext_weval h05 x hx _ (hy j)
          have hc_eq : dpPrefixCount p n d hd m' (fun j v b => s5.weval x (locW j v b)) (fun j => s5.weval x (yW j)) (Function.update pf1 m' false) =
              dpPrefixCount p n d hd m' (fun j v b => s.weval x (locW j v b)) (fun j => s.weval x (yW j)) (Function.update pf2 m' false) := by
            rw [hloc5, hy5, dpPrefixCount_spec p n d hp hd hdn m' (by omega), dpPrefixCount_spec p n d hp hd hdn m' (by omega)]
            congr 1; ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine and_congr_left fun _ => forall₃_congr fun pos _ hpos => ?_
            by_cases heq : pos = m'
            · simp [heq]
            · simp [Function.update_of_ne heq, hpf pos hpos]
          simp only [hc_eq]
          split_ifs
          · exact ihm (by omega) r' _ _ (fun pos hpos => by
              by_cases heq : pos = m' <;> simp [heq, Function.update_of_ne, hpf pos hpos])
          · exact ihm (by omega) _ _ _ (fun pos hpos => by
              by_cases heq : pos = m' <;> simp [heq, Function.update_of_ne, hpf pos hpos])
      dsimp only [unrankLoop]
      rw [hremNext_ev] at hrec_ev
      have hc := hunrank_congr m (by omega)
        (if bvVal s x remBv < dpPrefixCount p n d hd m (fun j v b => s.weval x (locW j v b))
            (fun j => s.weval x (yW j)) (Function.update (fun pos => s.weval x (prefW pos)) m false) then
          bvVal s x remBv
        else bvVal s x remBv - dpPrefixCount p n d hd m (fun j v b => s.weval x (locW j v b))
            (fun j => s.weval x (yW j)) (Function.update (fun pos => s.weval x (prefW pos)) m false))
        (fun pos => s5.weval x (Function.update prefW m bitW pos))
        (Function.update (fun pos => s.weval x (prefW pos)) m
          (!(decide (bvVal s x remBv < dpPrefixCount p n d hd m (fun j v b => s.weval x (locW j v b))
            (fun j => s.weval x (yW j)) (Function.update (fun pos => s.weval x (prefW pos)) m false)))))
        hpref5_ev
      split_ifs with hlt
      · simp only [hlt, decide_true, Bool.not_true, ↓reduceIte] at hrec_ev hc ⊢
        exact ⟨hrec_ev.1.trans hc.1, fun pos hpos => (hrec_ev.2 pos hpos).trans (hc.2 pos hpos)⟩
      · simp only [hlt, decide_false, Bool.not_false, ↓reduceIte] at hrec_ev hc ⊢
        exact ⟨hrec_ev.1.trans hc.1, fun pos hpos => (hrec_ev.2 pos hpos).trans (hc.2 pos hpos)⟩

def CState.empty (n_in : ℕ) : CState n_in := ⟨[]⟩

lemma CState.empty_valid (n_in : ℕ) : (CState.empty n_in).Valid :=
  ⟨by intro _ h; simp [CState.empty] at h,
   by intro j hj; simp [CState.empty] at hj⟩

lemma CState.empty_weval {n_in : ℕ} (x : List Bool) (w : ℕ) :
    (CState.empty n_in).weval x w = x.getD w false := rfl

lemma CState.toCircuit_spec {n_in : ℕ} (s : CState n_in) (hs : s.Valid) (out : ℕ) :
    let C : Circuit := ⟨s.gates, out⟩
    FanInTwo C ∧ ReadsBack n_in C ∧ C.size = s.gates.length ∧ ∀ x, C.eval x = s.weval x out :=
  ⟨hs.1, hs.2, rfl, fun _ => rfl⟩

lemma list_getD_append_left (l₁ l₂ : List Bool) (i : ℕ) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i false = l₁.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

lemma list_getD_append_right (l₁ l₂ : List Bool) (i : ℕ) (hi : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i false = l₂.getD (i - l₁.length) false := by
  simp [List.getD, List.getElem?_append_right hi]

def bitsOp (a x : ℕ) : List Bool := (List.range a).map (fun i => x.testBit i)

lemma bitsOp_length (a x : ℕ) : (bitsOp a x).length = a := by
  simp [bitsOp]

lemma bitsOp_getD (a x i : ℕ) (hi : i < a) : (bitsOp a x).getD i false = x.testBit i := by
  simp [bitsOp, List.getD, hi]

lemma flatMap_finRange_length {m n : ℕ} (f : Fin m → List Bool) (hf : ∀ i, (f i).length = n) :
    ((List.finRange m).flatMap f).length = m * n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.finRange_succ, List.flatMap_cons, List.length_append, hf 0,
      List.flatMap_map, ih (fun i => f i.succ) (fun i => hf i.succ)]
    rw [Nat.add_mul, one_mul, Nat.add_comm]

lemma flatMap_finRange_getD {m n : ℕ} (f : Fin m → List Bool) (hf : ∀ i, (f i).length = n)
    (j : Fin m) (u : ℕ) (hu : u < n) :
    ((List.finRange m).flatMap f).getD (j.val * n + u) false = (f j).getD u false := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    refine Fin.cases ?_ ?_ j
    · simp only [Fin.val_zero, zero_mul, zero_add]
      exact list_getD_append_left _ _ u (by rw [hf 0]; exact hu)
    · intro j'
      have hge : (f 0).length ≤ j'.succ.val * n + u := by
        rw [hf 0, Fin.val_succ, Nat.add_mul, one_mul]; omega
      rw [list_getD_append_right _ _ _ hge, hf 0]
      have hsub : j'.succ.val * n + u - n = j'.val * n + u := by
        rw [Fin.val_succ, Nat.add_mul, one_mul]; omega
      rw [hsub]
      exact ih (fun i => f i.succ) (fun i => hf i.succ) j'

lemma bvVal_eq_of_testBit {n_in L : ℕ} (s : CState n_in) (x : List Bool) (v : BVec L)
    (val : ℕ) (hval : val < 2 ^ L) (hbit : ∀ i : Fin L, s.weval x (v i) = val.testBit i.val) :
    bvVal s x v = val := by
  have h1 : bvVal s x v = (bitsToFin L (fun i => val.testBit i)).val := by
    dsimp only [bvVal, bitsToFin]
    apply Finset.sum_congr rfl; intro i _
    rw [hbit i]
  rw [h1]
  apply Nat.eq_of_testBit_eq; intro pos
  by_cases hpos : pos < L
  · exact bitsToFin_testBit L (fun i => val.testBit i) pos hpos
  · have hlt1 : (bitsToFin L (fun i => val.testBit i)).val < 2 ^ pos :=
      lt_of_lt_of_le (bitsToFin L _).isLt (Nat.pow_le_pow_right (by omega) (by omega))
    have hlt2 : val < 2 ^ pos :=
      lt_of_lt_of_le hval (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow hlt1, Nat.testBit_lt_two_pow hlt2]

def mkMuxFinL {n_in L : ℕ} (s : CState n_in) (sel : BVec L) (vals : Fin L → ℕ) :
    CState n_in × ℕ :=
  let (s0, z) := mkConst s false
  (List.finRange L).foldl (fun (st : CState n_in × ℕ) (v : Fin L) =>
    let (s1, eqv) := mkBvEqConstAux L st.1 sel v.val
    mkIte s1 eqv (vals v) st.2) (s0, z)

lemma mkMuxFinL_spec {n_in L : ℕ} (s : CState n_in) (hs : s.Valid)
    (sel : BVec L) (vals : Fin L → ℕ)
    (hsel : ∀ i, sel i < s.nw) (hvals : ∀ v, vals v < s.nw) :
    let res := mkMuxFinL s sel vals
    s.Ext res.1 ∧ res.1.Valid ∧ res.2 < res.1.nw ∧
    res.1.gates.length ≤ s.gates.length + 1 + L * (2 * L + 5) ∧
    ∀ x : List Bool, x.length = n_in → ∀ j : Fin L, bvVal s x sel = j.val →
      res.1.weval x res.2 = s.weval x (vals j) := by
  dsimp only [mkMuxFinL]
  have h0 := mkConst_spec s hs false
  set s0 := (mkConst s false).1; set z := (mkConst s false).2
  have hfold := foldl_cstate_spec (List.finRange L)
    (fun (st : CState n_in × ℕ) (v : Fin L) =>
      let (s1, eqv) := mkBvEqConstAux L st.1 sel v.val
      mkIte s1 eqv (vals v) st.2)
    (fun s' w pref => s.Ext s' ∧ w < s'.nw ∧
      ∀ x : List Bool, x.length = n_in → ∀ j : Fin L, bvVal s x sel = j.val →
        s'.weval x w = if j ∈ pref then s.weval x (vals j) else false)
    (2 * L + 5)
    (by
      intro s' w v pref hs' _ ⟨hext, hw, hev⟩
      have h1 := mkBvEqConst_spec L s' hs' sel v.val (lt_trans v.isLt Nat.lt_two_pow_self)
        (fun i => lt_of_lt_of_le (hsel i) (CState.ext_nw hext))
      set s1 := (mkBvEqConstAux L s' sel v.val).1; set eqv := (mkBvEqConstAux L s' sel v.val).2
      have hext1 : s.Ext s1 := CState.ext_trans hext h1.1
      have h2 := mkIte_spec s1 h1.2.1 eqv (vals v) w h1.2.2.1
        (lt_of_lt_of_le (hvals v) (CState.ext_nw hext1)) (lt_of_lt_of_le hw (CState.ext_nw h1.1))
      refine ⟨CState.ext_trans h1.1 h2.1, h2.2.1,
        by have := h1.2.2.2.1; have := h2.2.2.2.1; dsimp only [s1, eqv] at *; omega,
        CState.ext_trans hext1 h2.1, h2.2.2.1, ?_⟩
      intro x hx j hj
      rw [h2.2.2.2.2 x hx, h1.2.2.2.2 x hx, bvVal_ext hext x hx sel hsel, hj,
        CState.ext_weval hext1 x hx (vals v) (hvals v), CState.ext_weval h1.1 x hx w hw, hev x hx j hj]
      by_cases hveq : j = v
      · subst hveq; simp
      · have hne : j.val ≠ v.val := fun h => hveq (Fin.ext h)
        simp [hne, hveq])
    s0 h0.2.1 z [] ⟨h0.1, h0.2.2.1, fun x hx _ _ => by simp only [List.not_mem_nil, ↓reduceIte]; exact h0.2.2.2.2 x hx⟩
  refine ⟨CState.ext_trans h0.1 hfold.1, hfold.2.1, hfold.2.2.2.2.1, ?_, ?_⟩
  · have := h0.2.2.2.1; have := hfold.2.2.1; simp only [List.length_finRange] at this
    dsimp only [s0] at *; omega
  · intro x hx j hj
    have h := hfold.2.2.2.2.2 x hx j hj
    simp only [List.nil_append, List.mem_finRange, ↓reduceIte] at h
    exact h

def mkFullCircuit (p n r d : ℕ) (hd : 0 < d) : Circuit :=
  let k := p * n
  let L := k + 1
  let n_in := 4 * n + 2 * r * n + 2 * L + 1
  let nrW : ℕ → ℕ := fun u => u % n
  let ncW : ℕ → ℕ := fun u => n + u % n
  let crW : Fin r → ℕ → ℕ := fun jj u => 2 * n + jj.val * n + u % n
  let ccW : Fin r → ℕ → ℕ := fun jj u => 2 * n + r * n + jj.val * n + u % n
  let bankW : ℕ → ℕ := fun i => 2 * n + 2 * r * n + i
  let yW : Fin n → ℕ := fun i => 3 * n + 2 * r * n + i.val
  let tBv : BVec L := fun i => 4 * n + 2 * r * n + i.val
  let jBv : BVec L := fun i => 4 * n + 2 * r * n + L + i.val
  let modeW : ℕ := 4 * n + 2 * r * n + 2 * L
  let s0 := CState.empty n_in
  let (s1, validW) := mkValidAux r d bankW n s0
  let (s2, locW) := mkLocTable n r d nrW ncW crW ccW (fun i => bankW i.val) s1
  let (s3, w0) := mkConst s2 false
  let (s4, w1) := mkConst s3 true
  let (s5, c0Top) := mkPrefixCount p n d hd (k - 1) L locW yW (fun _ => w0) s4
  let (s6, c1Top) := mkPrefixCount p n d hd (k - 1) L locW yW (Function.update (fun _ => w0) (k - 1) w1) s5
  let (s7, cntBv) := mkBvAdd s6 c0Top c1Top
  let (s8, _, prefEnd) := mkUnrankLoop p n d hd L locW yW k s7 tBv (fun _ => w0)
  let (s9, tLtCntW) := mkBvLtAux L s8 tBv cntBv
  let (s10, cntBitW) := mkMuxFinL s9 jBv cntBv
  let (s11, unrBitW) := mkMuxFinL s10 jBv (fun jj => if jj.val = 0 then w1 else prefEnd (jj.val - 1))
  let (s12, unrOutW) := mkAnd s11 tLtCntW unrBitW
  let (s13, modeOutW) := mkIte s12 modeW cntBitW unrOutW
  let (s14, finalW) := mkAnd s13 validW modeOutW
  ⟨s14.gates, finalW⟩

set_option maxHeartbeats 800000 in

lemma fullCircuit_size_bound (p n r d : ℕ) (hp : 2 ≤ p) (hd : 0 < d) (hdn : d < n) (hr : 4 ≤ r) :
    let k := p * n
    let L := k + 1
    let D := 2 ^ d
    let H_b := (p + D ^ 3).choose p
    let initCost := 2 + D * (1 + d * 8 + H_b * (2 + 4 * L))
    let stepCost := (2 + p * (2 * (1 + D * (2 * d + 5)) + 9)) + 5 +
      (4 + D * (D * D * (3 + H_b * ((p + 1) * (40 * (L + 1) ^ 2))) + 2 * (6 + H_b * (21 * L + 1))))
    let diagCost := H_b * (2 + D * (2 * d + 1 + 4 * L) + 13 * L + 1)
    let prefCost := 4 + D * (1 + d * 8 + initCost + n * stepCost + diagCost + 4 * L + 13 * L + 1)
    (7 * n + 1) + (1 + 2 * n * D * (2 * (6 + 48 * r) * (7 * r + 2) + 4)) + 2 +
      prefCost + prefCost + (13 * L + 1) + k * (prefCost + 28 * L + 4) +
      (10 * L + 1) + (1 + L * (2 * L + 5)) + (1 + L * (2 * L + 5)) + 6 ≤
      2 ^ 56 * (k + r + D + 5) ^ 24 * H_b := by
  intro k L D H_b initCost stepCost diagCost prefCost
  set M := k + r + D + 5 with hM_def
  have hM5 : 5 ≤ M := by rw [hM_def]; exact Nat.le_add_left 5 (k + r + D)
  have hM1 : 1 ≤ M := by omega
  have hM0 : 0 < M := by omega
  have hH1 : 1 ≤ H_b := Nat.choose_pos (Nat.le_add_right p (D ^ 3))
  have hpk : p ≤ k := Nat.le_mul_of_pos_right p (by omega)
  have hnk : n ≤ k := Nat.le_mul_of_pos_left n (by omega)
  have hdD : d ≤ D := le_of_lt Nat.lt_two_pow_self
  have hpM : p ≤ M := by rw [hM_def]; omega
  have hnM : n ≤ M := by rw [hM_def]; omega
  have hdM : d ≤ M := by rw [hM_def]; omega
  have hrM : r ≤ M := by rw [hM_def]; omega
  have hDM : D ≤ M := by rw [hM_def]; omega
  have hkM : k ≤ M := by rw [hM_def]; omega
  have hLM : L ≤ M := by rw [hM_def]; dsimp [L]; omega
  have hL1M : L + 1 ≤ M := by rw [hM_def]; dsimp [L]; omega
  have hp1M : p + 1 ≤ M := by rw [hM_def]; omega
  have hpow_mono : ∀ a b, a ≤ b → M ^ a ≤ M ^ b := fun a b hab => Nat.pow_le_pow_right hM1 hab
  have hM_pow : ∀ b, 1 ≤ b → M ≤ M ^ b := fun b hb => by simpa using hpow_mono 1 b hb
  have hscale : ∀ c a b, a ≤ b → c * M ^ a * H_b ≤ c * M ^ b * H_b := fun c a b hab =>
    Nat.mul_le_mul_right H_b (Nat.mul_le_mul_left c (hpow_mono a b hab))
  have h1_le_MH : ∀ c a, c ≤ c * M ^ a * H_b := fun c a => by
    have h1 : 1 ≤ M ^ a * H_b := Nat.mul_pos (Nat.pow_pos hM0) hH1
    have := Nat.mul_le_mul_left c h1
    simpa [mul_assoc] using this

  have hinit : initCost ≤ 16 * M ^ 2 * H_b := by
    have h1 : 1 + d * 8 ≤ 9 * M := by omega
    have h2 : 9 * M ≤ 9 * M * H_b := Nat.le_mul_of_pos_right _ hH1
    have h3 : H_b * (2 + 4 * L) ≤ H_b * (6 * M) := Nat.mul_le_mul_left H_b (by omega)
    have h4 : 1 + d * 8 + H_b * (2 + 4 * L) ≤ 15 * M * H_b := by
      have h3' : H_b * (2 + 4 * L) ≤ 6 * M * H_b := by linarith
      have h2' : 1 + d * 8 ≤ 9 * M * H_b := le_trans h1 h2
      linarith
    have h5 : D * (1 + d * 8 + H_b * (2 + 4 * L)) ≤ 15 * M ^ 2 * H_b := by
      have := Nat.mul_le_mul hDM h4
      have hring : M * (15 * M * H_b) = 15 * M ^ 2 * H_b := by ring
      linarith
    have h7 : 2 ≤ 1 * M ^ 2 * H_b := le_trans (by omega : 2 ≤ M)
      (by simpa [one_mul] using le_trans (hM_pow 2 (by omega)) (Nat.le_mul_of_pos_right _ hH1))
    dsimp only [initCost]; linarith

  have hdiag : diagCost ≤ 16 * M ^ 2 * H_b := by
    have h1 : D * (2 * d + 1 + 4 * L) ≤ 7 * M ^ 2 := by
      have := Nat.mul_le_mul hDM (by omega : 2 * d + 1 + 4 * L ≤ 7 * M)
      have : M * (7 * M) = 7 * M ^ 2 := by ring
      linarith
    have h2 : 2 + 13 * L + 1 ≤ 9 * M ^ 2 := by
      have ha : 2 + 13 * L + 1 ≤ 16 * M := by omega
      have hb : 5 * M ≤ M * M := Nat.mul_le_mul_right M hM5
      have hc : M ^ 2 = M * M := by ring
      linarith
    have h5 : 2 + D * (2 * d + 1 + 4 * L) + 13 * L + 1 ≤ 16 * M ^ 2 := by linarith
    have h6 : H_b * (2 + D * (2 * d + 1 + 4 * L) + 13 * L + 1) ≤ H_b * (16 * M ^ 2) :=
      Nat.mul_le_mul_left H_b h5
    dsimp only [diagCost]; linarith

  have hstep : stepCost ≤ 128 * M ^ 6 * H_b := by
    have ha1 : D * (2 * d + 5) ≤ 7 * M ^ 2 := by
      have := Nat.mul_le_mul hDM (by omega : 2 * d + 5 ≤ 7 * M)
      have : M * (7 * M) = 7 * M ^ 2 := by ring
      linarith
    have ha3 : 11 ≤ 11 * M ^ 2 := le_trans (by omega : 11 ≤ 11 * 1) (Nat.mul_le_mul_left 11 (Nat.pow_pos hM0))
    have ha4 : 2 * (1 + D * (2 * d + 5)) + 9 ≤ 25 * M ^ 2 := by linarith
    have ha5 : p * (2 * (1 + D * (2 * d + 5)) + 9) ≤ 25 * M ^ 3 := by
      have := Nat.mul_le_mul hpM ha4
      have : M * (25 * M ^ 2) = 25 * M ^ 3 := by ring
      linarith
    have ha7 : 2 + 5 + 4 ≤ 11 * M ^ 3 := le_trans (by omega : 11 ≤ 11 * 1) (Nat.mul_le_mul_left 11 (Nat.pow_pos hM0))
    have ha8 : (2 + p * (2 * (1 + D * (2 * d + 5)) + 9)) + 5 + 4 ≤ 36 * M ^ 3 := by linarith
    have ha9 : 36 * M ^ 3 ≤ 25 * M ^ 6 * H_b := by
      have h2 : 5 * M ^ 3 ≤ M * M ^ 3 := Nat.mul_le_mul_right (M ^ 3) hM5
      have h3 : M * M ^ 3 = M ^ 4 := by ring
      have h4 : M ^ 4 ≤ M ^ 6 := hpow_mono 4 6 (by omega)
      have h5 : 25 * M ^ 6 ≤ 25 * M ^ 6 * H_b := Nat.le_mul_of_pos_right _ hH1
      linarith
    have hb1 : (L + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hL1M 2
    have hb2 : (p + 1) * (40 * (L + 1) ^ 2) ≤ 40 * M ^ 3 := by
      have := Nat.mul_le_mul hp1M (Nat.mul_le_mul_left 40 hb1)
      have : M * (40 * M ^ 2) = 40 * M ^ 3 := by ring
      linarith
    have hb4 : H_b * ((p + 1) * (40 * (L + 1) ^ 2)) ≤ 40 * M ^ 3 * H_b := by
      have := Nat.mul_le_mul_left H_b hb2
      have : H_b * (40 * M ^ 3) = 40 * M ^ 3 * H_b := by ring
      linarith
    have hb6 : 3 ≤ 3 * M ^ 3 * H_b := h1_le_MH 3 3
    have hb7 : 3 + H_b * ((p + 1) * (40 * (L + 1) ^ 2)) ≤ 43 * M ^ 3 * H_b := by linarith
    have hb8 : D * D ≤ M ^ 2 := by
      have := Nat.mul_le_mul hDM hDM
      have : M * M = M ^ 2 := by ring
      linarith
    have hb9 : D * D * (3 + H_b * ((p + 1) * (40 * (L + 1) ^ 2))) ≤ 43 * M ^ 5 * H_b := by
      have := Nat.mul_le_mul hb8 hb7
      have : M ^ 2 * (43 * M ^ 3 * H_b) = 43 * M ^ 5 * H_b := by ring
      linarith
    have hb11 : H_b * (21 * L + 1) ≤ 22 * M * H_b := by
      have := Nat.mul_le_mul_left H_b (by omega : 21 * L + 1 ≤ 22 * M)
      have : H_b * (22 * M) = 22 * M * H_b := by ring
      linarith
    have hb13 : 12 ≤ 12 * M * H_b := by simpa using h1_le_MH 12 1
    have hb14 : 2 * (6 + H_b * (21 * L + 1)) ≤ 60 * M * H_b := by linarith
    have hb15 : 60 * M * H_b ≤ 60 * M ^ 5 * H_b := by simpa using hscale 60 1 5 (by omega)
    have hb16 : D * D * (3 + H_b * ((p + 1) * (40 * (L + 1) ^ 2))) + 2 * (6 + H_b * (21 * L + 1)) ≤
        103 * M ^ 5 * H_b := by linarith
    have hb17 : D * (D * D * (3 + H_b * ((p + 1) * (40 * (L + 1) ^ 2))) + 2 * (6 + H_b * (21 * L + 1))) ≤
        103 * M ^ 6 * H_b := by
      have := Nat.mul_le_mul hDM hb16
      have : M * (103 * M ^ 5 * H_b) = 103 * M ^ 6 * H_b := by ring
      linarith
    dsimp only [stepCost]; linarith

  have hpref : prefCost ≤ 200 * M ^ 8 * H_b := by
    have hns : n * stepCost ≤ 128 * M ^ 7 * H_b := by
      have := Nat.mul_le_mul hnM hstep
      have : M * (128 * M ^ 6 * H_b) = 128 * M ^ 7 * H_b := by ring
      linarith
    have hinit7 : initCost ≤ 16 * M ^ 7 * H_b := le_trans hinit (hscale 16 2 7 (by omega))
    have hdiag7 : diagCost ≤ 16 * M ^ 7 * H_b := le_trans hdiag (hscale 16 2 7 (by omega))
    have hrest : 1 + d * 8 + 4 * L + 13 * L + 1 ≤ 30 * M ^ 7 * H_b :=
      le_trans (by omega : 1 + d * 8 + 4 * L + 13 * L + 1 ≤ 30 * M)
        (le_trans (Nat.mul_le_mul_left 30 (hM_pow 7 (by omega))) (Nat.le_mul_of_pos_right _ hH1))
    have hinner : 1 + d * 8 + initCost + n * stepCost + diagCost + 4 * L + 13 * L + 1 ≤ 190 * M ^ 7 * H_b := by
      linarith
    have hmul : D * (1 + d * 8 + initCost + n * stepCost + diagCost + 4 * L + 13 * L + 1) ≤ 190 * M ^ 8 * H_b := by
      have := Nat.mul_le_mul hDM hinner
      have : M * (190 * M ^ 7 * H_b) = 190 * M ^ 8 * H_b := by ring
      linarith
    have h4 : 4 ≤ 10 * M ^ 8 * H_b := le_trans (by omega : 4 ≤ 10) (h1_le_MH 10 8)
    dsimp only [prefCost]; linarith

  have hloc : 1 + 2 * n * D * (2 * (6 + 48 * r) * (7 * r + 2) + 4) ≤ 4000 * M ^ 4 := by
    have h1 : (6 + 48 * r) * (7 * r + 2) ≤ 450 * M ^ 2 := by
      have := Nat.mul_le_mul (by omega : 6 + 48 * r ≤ 50 * M) (by omega : 7 * r + 2 ≤ 9 * M)
      have : (50 * M) * (9 * M) = 450 * M ^ 2 := by ring
      linarith
    have h3 : 4 ≤ 100 * M ^ 2 := le_trans (by omega : 4 ≤ 100 * 1) (Nat.mul_le_mul_left 100 (Nat.pow_pos hM0))
    have h4 : 2 * (6 + 48 * r) * (7 * r + 2) + 4 ≤ 1000 * M ^ 2 := by linarith
    have h5 : 2 * n * D ≤ 2 * M ^ 2 := by
      have := Nat.mul_le_mul hnM hDM
      have : 2 * (M * M) = 2 * M ^ 2 := by ring
      have : 2 * n * D = 2 * (n * D) := by ring
      linarith
    have h7 : 2 * n * D * (2 * (6 + 48 * r) * (7 * r + 2) + 4) ≤ 2000 * M ^ 4 := by
      have := Nat.mul_le_mul h5 h4
      have : (2 * M ^ 2) * (1000 * M ^ 2) = 2000 * M ^ 4 := by ring
      linarith
    have h9 : 1 ≤ 2000 * M ^ 4 := le_trans (by omega : 1 ≤ 2000 * 1) (Nat.mul_le_mul_left 2000 (Nat.pow_pos hM0))
    linarith

  have hkpref : k * (prefCost + 28 * L + 4) ≤ 240 * M ^ 9 * H_b := by
    have h2 : 28 * L + 4 ≤ 40 * M ^ 8 * H_b :=
      le_trans (by omega : 28 * L + 4 ≤ 40 * M)
        (le_trans (Nat.mul_le_mul_left 40 (hM_pow 8 (by omega))) (Nat.le_mul_of_pos_right _ hH1))
    have h3 : prefCost + 28 * L + 4 ≤ 240 * M ^ 8 * H_b := by linarith
    have h4 : k * (prefCost + 28 * L + 4) ≤ 240 * M ^ 9 * H_b := by
      have := Nat.mul_le_mul hkM h3
      have : M * (240 * M ^ 8 * H_b) = 240 * M ^ 9 * H_b := by ring
      linarith
    exact h4
  have hpref9 : prefCost ≤ 200 * M ^ 9 * H_b := le_trans hpref (hscale 200 8 9 (by omega))
  have hloc9 : 1 + 2 * n * D * (2 * (6 + 48 * r) * (7 * r + 2) + 4) ≤ 4000 * M ^ 9 * H_b :=
    le_trans hloc (le_trans (Nat.mul_le_mul_left 4000 (hpow_mono 4 9 (by omega))) (Nat.le_mul_of_pos_right _ hH1))
  have hmux : (7 * n + 1) + 2 + (13 * L + 1) + (10 * L + 1) + (1 + L * (2 * L + 5)) + (1 + L * (2 * L + 5)) + 6 ≤
      100 * M ^ 9 * H_b := by
    have h1 : L * (2 * L + 5) ≤ 7 * M ^ 2 := by
      have := Nat.mul_le_mul hLM (by omega : 2 * L + 5 ≤ 7 * M)
      have : M * (7 * M) = 7 * M ^ 2 := by ring
      linarith
    have h4 : 7 * n + 13 * L + 10 * L + 13 ≤ 45 * M ^ 2 :=
      le_trans (by omega : 7 * n + 13 * L + 10 * L + 13 ≤ 45 * M) (Nat.mul_le_mul_left 45 (hM_pow 2 (by omega)))
    have h5 : (7 * n + 1) + 2 + (13 * L + 1) + (10 * L + 1) + (1 + L * (2 * L + 5)) + (1 + L * (2 * L + 5)) + 6 ≤
        100 * M ^ 2 := by linarith
    exact le_trans h5 (le_trans (Nat.mul_le_mul_left 100 (hpow_mono 2 9 (by omega))) (Nat.le_mul_of_pos_right _ hH1))
  have htot : (7 * n + 1) + (1 + 2 * n * D * (2 * (6 + 48 * r) * (7 * r + 2) + 4)) + 2 +
      prefCost + prefCost + (13 * L + 1) + k * (prefCost + 28 * L + 4) +
      (10 * L + 1) + (1 + L * (2 * L + 5)) + (1 + L * (2 * L + 5)) + 6 ≤ 5000 * M ^ 9 * H_b := by
    linarith
  have hfinal : 5000 * M ^ 9 * H_b ≤ 2 ^ 56 * M ^ 24 * H_b := by
    apply Nat.mul_le_mul_right H_b
    exact Nat.mul_le_mul (by norm_num) (hpow_mono 9 24 (by omega))
  exact le_trans htot hfinal

set_option maxHeartbeats 800000 in

lemma xVec_eval_spec (p n r : ℕ) (hn : 0 < n)
    (nr nc : Fin (2 ^ n)) (cr cc : Fin r → Fin (2 ^ n)) (bank : Fin n → Bool) (y : Fin (2 ^ n))
    (t : Fin (2 ^ (p * n + 1))) (j : Fin (p * n + 1)) (countMode : Bool) :
    let L := p * n + 1
    let n_in := 4 * n + 2 * r * n + 2 * L + 1
    let s0 := CState.empty n_in
    let x : List Bool := bitsOp n nr.val ++ bitsOp n nc.val ++
      (List.finRange r).flatMap (fun jj => bitsOp n (cr jj).val) ++
      (List.finRange r).flatMap (fun jj => bitsOp n (cc jj).val) ++
      List.ofFn bank ++ bitsOp n y.val ++ bitsOp L t.val ++ bitsOp L j.val ++ [countMode]
    x.length = n_in ∧
    (∀ u, s0.weval x (u % n) = nr.val.testBit (u % n)) ∧
    (∀ u, s0.weval x (n + u % n) = nc.val.testBit (u % n)) ∧
    (∀ jj : Fin r, ∀ u, s0.weval x (2 * n + jj.val * n + u % n) = (cr jj).val.testBit (u % n)) ∧
    (∀ jj : Fin r, ∀ u, s0.weval x (2 * n + r * n + jj.val * n + u % n) = (cc jj).val.testBit (u % n)) ∧
    (∀ i : Fin n, s0.weval x (2 * n + 2 * r * n + i.val) = bank i) ∧
    (∀ i : Fin n, s0.weval x (3 * n + 2 * r * n + i.val) = y.val.testBit i.val) ∧
    (bvVal s0 x (fun i : Fin L => 4 * n + 2 * r * n + i.val) = t.val) ∧
    (bvVal s0 x (fun i : Fin L => 4 * n + 2 * r * n + L + i.val) = j.val) ∧
    (s0.weval x (4 * n + 2 * r * n + 2 * L) = countMode) := by
  intro L n_in s0 x
  have hcr_len : ((List.finRange r).flatMap (fun jj => bitsOp n (cr jj).val)).length = r * n :=
    flatMap_finRange_length _ (fun _ => bitsOp_length n _)
  have hcc_len : ((List.finRange r).flatMap (fun jj => bitsOp n (cc jj).val)).length = r * n :=
    flatMap_finRange_length _ (fun _ => bitsOp_length n _)
  have h2rn : 2 * r * n = r * n + r * n := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [x, List.length_append, bitsOp_length, hcr_len, hcc_len, List.length_ofFn,
      List.length_singleton, n_in]; ring
  · intro u; rw [CState.empty_weval]; dsimp only [x]
    have hu : u % n < n := Nat.mod_lt u hn
    simp only [List.append_assoc]
    rw [list_getD_append_left _ _ _ (by rw [bitsOp_length]; exact hu), bitsOp_getD _ _ _ hu]
  · intro u; rw [CState.empty_weval]; dsimp only [x]
    have hu : u % n < n := Nat.mod_lt u hn
    simp only [List.append_assoc]
    rw [list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      Nat.add_sub_cancel_left, list_getD_append_left _ _ _ (by rw [bitsOp_length]; exact hu),
      bitsOp_getD _ _ _ hu]
  · intro jj u; rw [CState.empty_weval]; dsimp only [x]
    have hu : u % n < n := Nat.mod_lt u hn
    have hidx : jj.val * n + u % n < r * n := by
      have : jj.val + 1 ≤ r := jj.isLt
      have := Nat.mul_le_mul_right n this; rw [Nat.add_mul, one_mul] at this; omega
    simp only [List.append_assoc]
    rw [list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length]
    have hsub : 2 * n + jj.val * n + u % n - n - n = jj.val * n + u % n := by omega
    rw [hsub, list_getD_append_left _ _ _ (by rw [hcr_len]; exact hidx),
      flatMap_finRange_getD _ (fun _ => bitsOp_length n _) jj (u % n) hu, bitsOp_getD _ _ _ hu]
  · intro jj u; rw [CState.empty_weval]; dsimp only [x]
    have hu : u % n < n := Nat.mod_lt u hn
    have hidx : jj.val * n + u % n < r * n := by
      have : jj.val + 1 ≤ r := jj.isLt
      have := Nat.mul_le_mul_right n this; rw [Nat.add_mul, one_mul] at this; omega
    simp only [List.append_assoc]
    rw [list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [hcr_len]; omega), hcr_len]
    have hsub : 2 * n + r * n + jj.val * n + u % n - n - n - r * n = jj.val * n + u % n := by omega
    rw [hsub, list_getD_append_left _ _ _ (by rw [hcc_len]; exact hidx),
      flatMap_finRange_getD _ (fun _ => bitsOp_length n _) jj (u % n) hu, bitsOp_getD _ _ _ hu]
  · intro i; rw [CState.empty_weval]; dsimp only [x]
    simp only [List.append_assoc]
    rw [list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [hcr_len]; omega), hcr_len,
      list_getD_append_right _ _ _ (by rw [hcc_len]; omega), hcc_len]
    have hsub : 2 * n + 2 * r * n + i.val - n - n - r * n - r * n = i.val := by omega
    rw [hsub, list_getD_append_left _ _ _ (by rw [List.length_ofFn]; exact i.isLt)]
    simp [List.getD, i.isLt]
  · intro i; rw [CState.empty_weval]; dsimp only [x]
    simp only [List.append_assoc]
    rw [list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [hcr_len]; omega), hcr_len,
      list_getD_append_right _ _ _ (by rw [hcc_len]; omega), hcc_len,
      list_getD_append_right _ _ _ (by rw [List.length_ofFn]; omega), List.length_ofFn]
    have hsub : 3 * n + 2 * r * n + i.val - n - n - r * n - r * n - n = i.val := by omega
    rw [hsub, list_getD_append_left _ _ _ (by rw [bitsOp_length]; exact i.isLt),
      bitsOp_getD _ _ _ i.isLt]
  · apply bvVal_eq_of_testBit s0 x _ t.val t.isLt
    intro i; rw [CState.empty_weval]; dsimp only [x]
    simp only [List.append_assoc]
    rw [list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [hcr_len]; omega), hcr_len,
      list_getD_append_right _ _ _ (by rw [hcc_len]; omega), hcc_len,
      list_getD_append_right _ _ _ (by rw [List.length_ofFn]; omega), List.length_ofFn,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length]
    have hsub : 4 * n + 2 * r * n + i.val - n - n - r * n - r * n - n - n = i.val := by omega
    rw [hsub, list_getD_append_left _ _ _ (by rw [bitsOp_length]; exact i.isLt),
      bitsOp_getD _ _ _ i.isLt]
  · apply bvVal_eq_of_testBit s0 x _ j.val (lt_trans j.isLt Nat.lt_two_pow_self)
    intro i; rw [CState.empty_weval]; dsimp only [x]
    simp only [List.append_assoc]
    rw [list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [hcr_len]; omega), hcr_len,
      list_getD_append_right _ _ _ (by rw [hcc_len]; omega), hcc_len,
      list_getD_append_right _ _ _ (by rw [List.length_ofFn]; omega), List.length_ofFn,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length]
    have hsub : 4 * n + 2 * r * n + L + i.val - n - n - r * n - r * n - n - n - L = i.val := by omega
    rw [hsub, list_getD_append_left _ _ _ (by rw [bitsOp_length]; exact i.isLt),
      bitsOp_getD _ _ _ i.isLt]
  · rw [CState.empty_weval]; dsimp only [x]
    simp only [List.append_assoc]
    rw [list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [hcr_len]; omega), hcr_len,
      list_getD_append_right _ _ _ (by rw [hcc_len]; omega), hcc_len,
      list_getD_append_right _ _ _ (by rw [List.length_ofFn]; omega), List.length_ofFn,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length,
      list_getD_append_right _ _ _ (by rw [bitsOp_length]; omega), bitsOp_length]
    have hsub : 4 * n + 2 * r * n + 2 * L - n - n - r * n - r * n - n - n - L - L = 0 := by omega
    rw [hsub]; rfl

lemma card_filter_eq_of_iff {α : Type*} (s : Finset α) (p q : α → Prop)
    {dp : DecidablePred p} {dq : DecidablePred q} (h : ∀ a ∈ s, p a ↔ q a) :
    (@Finset.filter α p dp s).card = (@Finset.filter α q dq s).card := by
  apply congrArg Finset.card
  exact Finset.ext fun a => by
    rw [@Finset.mem_filter α p dp s a, @Finset.mem_filter α q dq s a]
    exact and_congr_right (h a)

end PEqualNP.Outside.L_meta_33670

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_33670 : (∀ (p n r d : Nat), 2 ≤ p → 0 < d → d < n → 4 ≤ r →
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let k := p*n
  let D := 2^d
  let W := Fin (2^k)
  let Y := Fin (2^n)
  let tile := fun w : Nat => (List.range p).foldl (fun z a => z ||| (w <<< (a*n))) 0
  let rot := fun (h w : Nat) =>
    ((w <<< (h % k)) ||| (w >>> (k - h % k))) % 2^k
  let step := fun (w : Nat) =>
    (List.range k).foldl (fun acc i => acc ||| ((xor (w.testBit i)
      (!(w.testBit ((i+1)%k)) && w.testBit ((i+2)%k))).toNat <<< i)) 0
  let state := fun (col : Bool) (w name : Nat) (c : Fin r → Y) =>
    let g := if col then 2 else 1
    (List.finRange r).foldl (fun x j =>
      step (x ^^^ rot g x ^^^ rot (k-g) x) ^^^
        rot (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ tile (c j).val)
      (rot (if col then 3 else 1) w ^^^ name)
  let reach := fun col : Bool => if col then 7*r-2 else 5*r-3
  let delay := fun col : Bool => if col then 3*r+1 else 2*r-2
  let bits := fun (a x : Nat) => (List.range a).map (fun i => x.testBit i)
  let sched := fun (c : Fin r → Y) => (List.finRange r).flatMap (fun j => bits n (c j).val)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (4*n+2*r*n+2*(k+1)+1) C ∧
    C.size ≤ 2^56*(k+r+D+5)^24*((p+D^3).choose p) ∧
    ∀ (nr nc : Y) (cr cc : Fin r → Y) (bank : Fin n → Bool) (y : Y)
      (t : Fin (2^(k+1))) (j : Fin (k+1)) (countMode : Bool),
      let valid := ∀ i, reach (bank i) ≤ d
      let sensor := fun (w : W) (i : Fin n) (a : Fin p) =>
        let col := bank i
        let p0 := a.val*n+i.val
        (state col w.val (tile (if col then nc.val else nr.val))
          (if col then cc else cr)).testBit ((p0+delay col)%k)
      let hit := fun w : W => ∀ i : Fin n,
        (List.finRange p).foldl (fun b a => xor b (sensor w i a)) false = y.val.testBit i.val
      let cnt := Nat.card {w : W // hit w}
      C.eval (bits n nr.val ++ bits n nc.val ++ sched cr ++ sched cc ++ List.ofFn bank ++
        bits n y.val ++ bits (k+1) t.val ++ bits (k+1) j.val ++ [countMode]) =
        decide (valid ∧ (if countMode then cnt.testBit j.val = true else
          ∃ w : W, hit w ∧ Nat.card {z : W // z < w ∧ hit z} = t.val ∧
            (j.val = 0 ∨ w.val.testBit (j.val-1) = true)))) := by
  intro p n r d hp hd hdn hr
  open PEqualNP.Outside.L_meta_33670 in
  let k := p * n
  let L := k + 1
  let D := 2 ^ d
  let n_in := 4 * n + 2 * r * n + 2 * L + 1
  have hn : 0 < n := by omega
  have hk : 0 < k := Nat.mul_pos (by omega) hn
  have h2rn : 2 * r * n = r * n + r * n := by ring
  refine ⟨mkFullCircuit p n r d hd, ?_⟩

  dsimp only [mkFullCircuit]
  let nrW : ℕ → ℕ := fun u => u % n
  let ncW : ℕ → ℕ := fun u => n + u % n
  let crW : Fin r → ℕ → ℕ := fun jj u => 2 * n + jj.val * n + u % n
  let ccW : Fin r → ℕ → ℕ := fun jj u => 2 * n + r * n + jj.val * n + u % n
  let bankW : ℕ → ℕ := fun i => 2 * n + 2 * r * n + i
  let yW : Fin n → ℕ := fun i => 3 * n + 2 * r * n + i.val
  let tBv : BVec L := fun i => 4 * n + 2 * r * n + i.val
  let jBv : BVec L := fun i => 4 * n + 2 * r * n + L + i.val
  let modeW : ℕ := 4 * n + 2 * r * n + 2 * L
  let s0 := CState.empty n_in
  have hs0 : s0.Valid := CState.empty_valid n_in
  have hs0_nw : s0.nw = n_in := by simp [s0, CState.empty, CState.nw]
  have hnr_lt : ∀ u, nrW u < s0.nw := fun u => by
    rw [hs0_nw]; have := Nat.mod_lt u hn; dsimp [nrW, n_in]; omega
  have hnc_lt : ∀ u, ncW u < s0.nw := fun u => by
    rw [hs0_nw]; have := Nat.mod_lt u hn; dsimp [ncW, n_in]; omega
  have hcr_lt : ∀ jj u, crW jj u < s0.nw := fun jj u => by
    rw [hs0_nw]; have h1 := Nat.mod_lt u hn
    have h2 : jj.val * n + n ≤ r * n := by
      have : jj.val + 1 ≤ r := jj.isLt
      have := Nat.mul_le_mul_right n this; rw [Nat.add_mul, one_mul] at this; exact this
    dsimp [crW, n_in]; omega
  have hcc_lt : ∀ jj u, ccW jj u < s0.nw := fun jj u => by
    rw [hs0_nw]; have h1 := Nat.mod_lt u hn
    have h2 : jj.val * n + n ≤ r * n := by
      have : jj.val + 1 ≤ r := jj.isLt
      have := Nat.mul_le_mul_right n this; rw [Nat.add_mul, one_mul] at this; exact this
    dsimp [ccW, n_in]; omega
  have hbank_lt : ∀ i < n, bankW i < s0.nw := fun i hi => by
    rw [hs0_nw]; dsimp [bankW, n_in]; omega
  have hy_lt : ∀ i, yW i < s0.nw := fun i => by
    rw [hs0_nw]; have := i.isLt; dsimp [yW, n_in]; omega
  have ht_lt : ∀ i, tBv i < s0.nw := fun i => by
    rw [hs0_nw]; have := i.isLt; dsimp [tBv, n_in]; omega
  have hj_lt : ∀ i, jBv i < s0.nw := fun i => by
    rw [hs0_nw]; have := i.isLt; dsimp [jBv, n_in]; omega
  have hmode_lt : modeW < s0.nw := by
    rw [hs0_nw]; dsimp [modeW, n_in]; omega
  have h1 := mkValidAux_spec r d bankW n s0 hs0 hbank_lt
  set s1 := (mkValidAux r d bankW n s0).1; set validW := (mkValidAux r d bankW n s0).2
  have h2 := mkLocTable_spec n r d nrW ncW crW ccW (fun i => bankW i.val) s1 h1.2.1
    (fun u => lt_of_lt_of_le (hnr_lt u) (CState.ext_nw h1.1))
    (fun u => lt_of_lt_of_le (hnc_lt u) (CState.ext_nw h1.1))
    (fun jj u => lt_of_lt_of_le (hcr_lt jj u) (CState.ext_nw h1.1))
    (fun jj u => lt_of_lt_of_le (hcc_lt jj u) (CState.ext_nw h1.1))
    (fun i => lt_of_lt_of_le (hbank_lt i.val i.isLt) (CState.ext_nw h1.1))
  set s2 := (mkLocTable n r d nrW ncW crW ccW (fun i => bankW i.val) s1).1
  set locW := (mkLocTable n r d nrW ncW crW ccW (fun i => bankW i.val) s1).2
  have h02 : s0.Ext s2 := CState.ext_trans h1.1 h2.1
  have h3 := mkConst_spec s2 h2.2.1 false
  set s3 := (mkConst s2 false).1; set w0 := (mkConst s2 false).2
  have h4 := mkConst_spec s3 h3.2.1 true
  set s4 := (mkConst s3 true).1; set w1 := (mkConst s3 true).2
  have h24 : s2.Ext s4 := CState.ext_trans h3.1 h4.1
  have h04 : s0.Ext s4 := CState.ext_trans h02 h24
  have h5 := mkPrefixCount_spec p n d hp hd hdn (k - 1) L (by omega) locW yW (fun _ => w0) s4 h4.2.1
    (fun i v b => lt_of_lt_of_le (h2.2.2.1 i v b) (CState.ext_nw h24))
    (fun i => lt_of_lt_of_le (hy_lt i) (CState.ext_nw h04))
    (fun _ _ => lt_of_lt_of_le h3.2.2.1 (CState.ext_nw h4.1))
  set s5 := (mkPrefixCount p n d hd (k - 1) L locW yW (fun _ => w0) s4).1
  set c0Top := (mkPrefixCount p n d hd (k - 1) L locW yW (fun _ => w0) s4).2
  have h25 : s2.Ext s5 := CState.ext_trans h24 h5.1
  have h05 : s0.Ext s5 := CState.ext_trans h04 h5.1
  have h6 := mkPrefixCount_spec p n d hp hd hdn (k - 1) L (by omega) locW yW
    (Function.update (fun _ => w0) (k - 1) w1) s5 h5.2.1
    (fun i v b => lt_of_lt_of_le (h2.2.2.1 i v b) (CState.ext_nw h25))
    (fun i => lt_of_lt_of_le (hy_lt i) (CState.ext_nw h05))
    (fun pos _ => by
      by_cases heq : pos = k - 1
      · rw [heq, Function.update_self]; exact lt_of_lt_of_le h4.2.2.1 (CState.ext_nw h5.1)
      · rw [Function.update_of_ne heq]; exact lt_of_lt_of_le h3.2.2.1 (CState.ext_nw (CState.ext_trans h4.1 h5.1)))
  set s6 := (mkPrefixCount p n d hd (k - 1) L locW yW (Function.update (fun _ => w0) (k - 1) w1) s5).1
  set c1Top := (mkPrefixCount p n d hd (k - 1) L locW yW (Function.update (fun _ => w0) (k - 1) w1) s5).2
  have h7 := mkBvAdd_spec s6 h6.2.1 c0Top c1Top
    (fun i => lt_of_lt_of_le (h5.2.2.1 i) (CState.ext_nw h6.1)) h6.2.2.1
  set s7 := (mkBvAdd s6 c0Top c1Top).1; set cntBv := (mkBvAdd s6 c0Top c1Top).2
  have h47 : s4.Ext s7 := CState.ext_trans h5.1 (CState.ext_trans h6.1 h7.1)
  have h27 : s2.Ext s7 := CState.ext_trans h24 h47
  have h07 : s0.Ext s7 := CState.ext_trans h04 h47
  have h8 := mkUnrankLoop_spec p n d hp hd hdn locW yW k le_rfl s7 h7.2.1 tBv (fun _ => w0)
    (fun i v b => lt_of_lt_of_le (h2.2.2.1 i v b) (CState.ext_nw h27))
    (fun i => lt_of_lt_of_le (hy_lt i) (CState.ext_nw h07))
    (fun i => lt_of_lt_of_le (ht_lt i) (CState.ext_nw h07))
    (fun _ _ => lt_of_lt_of_le h3.2.2.1 (CState.ext_nw (CState.ext_trans h4.1 h47)))
  set s8 := (mkUnrankLoop p n d hd L locW yW k s7 tBv (fun _ => w0)).1
  set prefEnd := (mkUnrankLoop p n d hd L locW yW k s7 tBv (fun _ => w0)).2.2
  have h08 : s0.Ext s8 := CState.ext_trans h07 h8.1
  have h9 := mkBvLt_spec L s8 h8.2.1 tBv cntBv
    (fun i => lt_of_lt_of_le (ht_lt i) (CState.ext_nw h08))
    (fun i => lt_of_lt_of_le (h7.2.2.1 i) (CState.ext_nw h8.1))
  set s9 := (mkBvLtAux L s8 tBv cntBv).1; set tLtCntW := (mkBvLtAux L s8 tBv cntBv).2
  have h79 : s7.Ext s9 := CState.ext_trans h8.1 h9.1
  have h09 : s0.Ext s9 := CState.ext_trans h08 h9.1
  have h10 := mkMuxFinL_spec s9 h9.2.1 jBv cntBv
    (fun i => lt_of_lt_of_le (hj_lt i) (CState.ext_nw h09))
    (fun i => lt_of_lt_of_le (h7.2.2.1 i) (CState.ext_nw h79))
  set s10 := (mkMuxFinL s9 jBv cntBv).1; set cntBitW := (mkMuxFinL s9 jBv cntBv).2
  have h810 : s8.Ext s10 := CState.ext_trans h9.1 h10.1
  have h410 : s4.Ext s10 := CState.ext_trans h47 (CState.ext_trans h79 h10.1)
  have h010 : s0.Ext s10 := CState.ext_trans h09 h10.1
  have h11 := mkMuxFinL_spec s10 h10.2.1 jBv (fun jj => if jj.val = 0 then w1 else prefEnd (jj.val - 1))
    (fun i => lt_of_lt_of_le (hj_lt i) (CState.ext_nw h010))
    (fun jj => by
      split_ifs with hz
      · exact lt_of_lt_of_le h4.2.2.1 (CState.ext_nw h410)
      · exact lt_of_lt_of_le (h8.2.2.2.1 (jj.val - 1) (by have := jj.isLt; omega)) (CState.ext_nw h810))
  set s11 := (mkMuxFinL s10 jBv (fun jj => if jj.val = 0 then w1 else prefEnd (jj.val - 1))).1
  set unrBitW := (mkMuxFinL s10 jBv (fun jj => if jj.val = 0 then w1 else prefEnd (jj.val - 1))).2
  have h911 : s9.Ext s11 := CState.ext_trans h10.1 h11.1
  have h011 : s0.Ext s11 := CState.ext_trans h010 h11.1
  have h12 := mkAnd_spec s11 h11.2.1 tLtCntW unrBitW
    (lt_of_lt_of_le h9.2.2.1 (CState.ext_nw h911)) h11.2.2.1
  set s12 := (mkAnd s11 tLtCntW unrBitW).1; set unrOutW := (mkAnd s11 tLtCntW unrBitW).2
  have h1012 : s10.Ext s12 := CState.ext_trans h11.1 h12.1
  have h012 : s0.Ext s12 := CState.ext_trans h011 h12.1
  have h13 := mkIte_spec s12 h12.2.1 modeW cntBitW unrOutW
    (lt_of_lt_of_le hmode_lt (CState.ext_nw h012))
    (lt_of_lt_of_le h10.2.2.1 (CState.ext_nw h1012)) h12.2.2.1
  set s13 := (mkIte s12 modeW cntBitW unrOutW).1; set modeOutW := (mkIte s12 modeW cntBitW unrOutW).2
  have h113 : s1.Ext s13 := CState.ext_trans h2.1 (CState.ext_trans h27 (CState.ext_trans h79 (CState.ext_trans h10.1 (CState.ext_trans h1012 h13.1))))
  have h14 := mkAnd_spec s13 h13.2.1 validW modeOutW
    (lt_of_lt_of_le h1.2.2.1 (CState.ext_nw h113)) h13.2.2.1
  set s14 := (mkAnd s13 validW modeOutW).1; set finalW := (mkAnd s13 validW modeOutW).2
  have hcirc := CState.toCircuit_spec s14 h14.2.1 finalW
  refine ⟨hcirc.1, hcirc.2.1, ?_, ?_⟩
  ·
    rw [hcirc.2.2.1]
    have hg1 : s1.gates.length = s0.gates.length + 7 * n + 1 := h1.2.2.2.1
    have hg2 : s2.gates.length ≤ s1.gates.length + 1 + 2 * n * D * (2 * (6 + 48 * r) * (7 * r + 2) + 4) := h2.2.2.2.1
    have hg3 : s3.gates.length = s2.gates.length + 1 := h3.2.2.2.1
    have hg4 : s4.gates.length = s3.gates.length + 1 := h4.2.2.2.1
    let H_b := (p + D ^ 3).choose p
    let initCost := 2 + D * (1 + d * 8 + H_b * (2 + 4 * L))
    let stepCost := (2 + p * (2 * (1 + D * (2 * d + 5)) + 9)) + 5 +
      (4 + D * (D * D * (3 + H_b * ((p + 1) * (40 * (L + 1) ^ 2))) + 2 * (6 + H_b * (21 * L + 1))))
    let diagCost := H_b * (2 + D * (2 * d + 1 + 4 * L) + 13 * L + 1)
    let prefCost := 4 + D * (1 + d * 8 + initCost + n * stepCost + diagCost + 4 * L + 13 * L + 1)
    have hg5 : s5.gates.length ≤ s4.gates.length + prefCost := by
      have := h5.2.2.2.1; dsimp only [s5, prefCost, diagCost, stepCost, initCost, H_b, D] at *; omega
    have hg6 : s6.gates.length ≤ s5.gates.length + prefCost := by
      have := h6.2.2.2.1; dsimp only [s6, prefCost, diagCost, stepCost, initCost, H_b, D] at *; omega
    have hg7 : s7.gates.length = s6.gates.length + 13 * L + 1 := h7.2.2.2.1
    have hg8 : s8.gates.length ≤ s7.gates.length + k * (prefCost + 28 * L + 4) := by
      have := h8.2.2.2.2.1; dsimp only [s8, prefCost, diagCost, stepCost, initCost, H_b, D] at *; omega
    have hg9 : s9.gates.length = s8.gates.length + 10 * L + 1 := h9.2.2.2.1
    have hg10 : s10.gates.length ≤ s9.gates.length + 1 + L * (2 * L + 5) := h10.2.2.2.1
    have hg11 : s11.gates.length ≤ s10.gates.length + 1 + L * (2 * L + 5) := h11.2.2.2.1
    have hg12 : s12.gates.length = s11.gates.length + 1 := h12.2.2.2.1
    have hg13 : s13.gates.length = s12.gates.length + 4 := h13.2.2.2.1
    have hg14 : s14.gates.length = s13.gates.length + 1 := h14.2.2.2.1
    have hs0_len : s0.gates.length = 0 := rfl
    have hbd := fullCircuit_size_bound p n r d hp hd hdn hr
    have hsum : s14.gates.length ≤ (7 * n + 1) + (1 + 2 * n * D * (2 * (6 + 48 * r) * (7 * r + 2) + 4)) + 2 +
        prefCost + prefCost + (13 * L + 1) + k * (prefCost + 28 * L + 4) +
        (10 * L + 1) + (1 + L * (2 * L + 5)) + (1 + L * (2 * L + 5)) + 6 := by omega
    exact le_trans hsum hbd
  ·
    intro nr nc cr cc bank y t j countMode
    let x : List Bool := bitsOp n nr.val ++ bitsOp n nc.val ++
      (List.finRange r).flatMap (fun jj => bitsOp n (cr jj).val) ++
      (List.finRange r).flatMap (fun jj => bitsOp n (cc jj).val) ++
      List.ofFn bank ++ bitsOp n y.val ++ bitsOp L t.val ++ bitsOp L j.val ++ [countMode]
    rcases xVec_eval_spec p n r hn nr nc cr cc bank y t j countMode with
      ⟨hx, hev_nr, hev_nc, hev_cr, hev_cc, hev_bank, hev_y, ht_bv, hj_bv, hev_mode⟩

    have hvalid_ev : s1.weval x validW = decide (∀ i : Fin n, reachOp r (bank i) ≤ d) := by
      rw [h1.2.2.2.2 x hx]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      dsimp only [bankW]
      exact ⟨fun h i => by have := h i.val i.isLt; rw [hev_bank i] at this; exact this,
        fun h i hi => by have := h ⟨i, hi⟩; rw [← hev_bank ⟨i, hi⟩] at this; exact this⟩

    change (⟨s14.gates, finalW⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval x = _
    rw [hcirc.2.2.2 x, h14.2.2.2.2 x hx, CState.ext_weval h113 x hx validW h1.2.2.1, hvalid_ev]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]

    have hreach_eq : ∀ col : Bool,
        @ite ℕ (col = true) (Classical.propDecidable _) (7 * r - 2) (5 * r - 3) = reachOp r col :=
      fun col => by cases col <;> simp [reachOp]
    by_cases hval : ∀ i : Fin n, reachOp r (bank i) ≤ d
    · refine and_congr (⟨fun _ i => by rw [hreach_eq]; exact hval i, fun _ => hval⟩) ?_

      let locFn : Fin n → Fin D → Bool → Bool := fun i v b =>
        locSensor n r d (bank i)
          (fun u => (if bank i then nc else nr).val.testBit (u % n))
          (fun jj u => (if bank i then cc else cr) jj |>.val.testBit (u % n))
          i.val v b
      let yFn : Fin n → Bool := fun i => y.val.testBit i.val

      have hloc_ev : ∀ i v b, s2.weval x (locW i v b) = locFn i v b := by
        intro i v b
        rw [h2.2.2.2.2 x hx i v b, CState.ext_weval h1.1 x hx (bankW i.val) (hbank_lt i.val i.isLt), hev_bank i]
        dsimp only [locFn]
        congr 1
        · funext u; split_ifs with hb
          · rw [CState.ext_weval h1.1 x hx (ncW u) (hnc_lt u), hev_nc u]
          · rw [CState.ext_weval h1.1 x hx (nrW u) (hnr_lt u), hev_nr u]
        · funext jj u; split_ifs with hb
          · rw [CState.ext_weval h1.1 x hx (ccW jj u) (hcc_lt jj u), hev_cc jj u]
          · rw [CState.ext_weval h1.1 x hx (crW jj u) (hcr_lt jj u), hev_cr jj u]

      have hsensor_eq : ∀ (w : Fin (2 ^ k)) (i : Fin n) (a : Fin p),
          let col := bank i
          let p0 := a.val * n + i.val
          ((List.finRange r).foldl (fun z jj =>
            stepOp k (z ^^^ rotOp k (if col then 2 else 1) z ^^^ rotOp k (k - if col then 2 else 1) z) ^^^
              rotOp k (if col then 3 * (jj.val + 1) + 1 else 2 * jj.val) w.val ^^^
              tileOp p n ((if col then cc else cr) jj).val)
            (rotOp k (if col then 3 else 1) w.val ^^^ tileOp p n (if col then nc.val else nr.val))).testBit
            ((p0 + delayOp r col) % k) =
            locFn i (winOf k d w p0) (w.val.testBit ((p0 + d) % k)) := by
        intro w i a col p0
        rw [← stateAux_eq_foldl p n r col w.val (tileOp p n (if col then nc.val else nr.val)) (if col then cc else cr)]
        have hname_eq : (if col then nc.val else nr.val) = (if col then nc else nr).val := by
          cases col <;> rfl
        rw [hname_eq, locState_eq_stateAux p n r d hp hd hdn hr col (hval i) w (if col then nc else nr) (if col then cc else cr) i a]
        dsimp only [locFn, locSensor]
        have hcongr1 := locState_congr n r d hr col (hval i)
          (fun idx => w.val.testBit ((p0 + idx) % k))
          (fun idx => if idx < d then (winOf k d w p0).val.testBit idx else w.val.testBit ((p0 + d) % k))
          (fun idx hidx => by
            by_cases hlt : idx < d
            · rw [if_pos hlt, winOf_testBit k d w p0 idx hlt]
            · have heq : idx = d := by omega
              rw [if_neg hlt, heq])
          (fun u => (if col then nc else nr).val.testBit u)
          (fun jj u => ((if col then cc else cr) jj).val.testBit u) i.val
        rw [hcongr1]

        have hmod_congr : ∀ t q,
            locState n r col (fun idx => if idx < d then (winOf k d w p0).val.testBit idx else w.val.testBit ((p0 + d) % k))
              (fun u => (if col then nc else nr).val.testBit u)
              (fun jj u => ((if col then cc else cr) jj).val.testBit u) i.val t q =
            locState n r col (fun idx => if idx < d then (winOf k d w p0).val.testBit idx else w.val.testBit ((p0 + d) % k))
              (fun u => (if col then nc else nr).val.testBit (u % n))
              (fun jj u => ((if col then cc else cr) jj).val.testBit (u % n)) i.val t q := by
          intro t; induction t with
          | zero => intro q; simp only [locState, Nat.mod_mod]
          | succ t' iht => intro q; simp only [locState, Nat.mod_mod, iht]
        exact hmod_congr r (delayOp r col)
      have hsensor_cl : ∀ (w : Fin (2 ^ k)) (i : Fin n) (a : Fin p),
          letI : ∀ P : Prop, Decidable P := Classical.propDecidable
          ((List.finRange r).foldl (fun z jj =>
            stepOp k (z ^^^ rotOp k (if bank i then 2 else 1) z ^^^ rotOp k (k - if bank i then 2 else 1) z) ^^^
              rotOp k (if bank i then 3 * (jj.val + 1) + 1 else 2 * jj.val) w.val ^^^
              tileOp p n ((if bank i then cc else cr) jj).val)
            (rotOp k (if bank i then 3 else 1) w.val ^^^ tileOp p n (if bank i then nc.val else nr.val))).testBit
            ((a.val * n + i.val + if bank i then 3 * r + 1 else 2 * r - 2) % k) =
          locFn i (winOf k d w (a.val * n + i.val)) (w.val.testBit ((a.val * n + i.val + d) % k)) := by
        intro w i a
        have h0 := hsensor_eq w i a
        dsimp only [delayOp] at h0
        cases hbi : bank i <;> simpa [hbi] using h0
      have hhit_iff : ∀ w : Fin (2 ^ k),
          (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
           ∀ i : Fin n, (List.finRange p).foldl (fun b a =>
            xor b (((List.finRange r).foldl (fun z jj =>
              stepOp k (z ^^^ rotOp k (if bank i then 2 else 1) z ^^^ rotOp k (k - if bank i then 2 else 1) z) ^^^
                rotOp k (if bank i then 3 * (jj.val + 1) + 1 else 2 * jj.val) w.val ^^^
                tileOp p n ((if bank i then cc else cr) jj).val)
              (rotOp k (if bank i then 3 else 1) w.val ^^^ tileOp p n (if bank i then nc.val else nr.val))).testBit
              ((a.val * n + i.val + if bank i then 3 * r + 1 else 2 * r - 2) % k))) false = y.val.testBit i.val) ↔
          hitLoc p n d locFn yFn w := by
        intro w
        refine forall_congr' fun i => ?_
        have hfold_eq :
            (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
             (List.finRange p).foldl (fun b a =>
              xor b (((List.finRange r).foldl (fun z jj =>
                stepOp k (z ^^^ rotOp k (if bank i then 2 else 1) z ^^^ rotOp k (k - if bank i then 2 else 1) z) ^^^
                  rotOp k (if bank i then 3 * (jj.val + 1) + 1 else 2 * jj.val) w.val ^^^
                  tileOp p n ((if bank i then cc else cr) jj).val)
                (rotOp k (if bank i then 3 else 1) w.val ^^^ tileOp p n (if bank i then nc.val else nr.val))).testBit
                ((a.val * n + i.val + if bank i then 3 * r + 1 else 2 * r - 2) % k))) false) =
            (List.finRange p).foldl (fun b a =>
              xor b (locFn i (winOf k d w (a.val * n + i.val)) (w.val.testBit ((a.val * n + i.val + d) % k)))) false := by
          congr 1; funext b a; rw [hsensor_cl w i a]
        rw [hfold_eq]

      have : DecidablePred (hitLoc p n d locFn yFn) := Classical.decPred _
      let cnt := (Finset.univ.filter fun w : Fin (2 ^ k) => hitLoc p n d locFn yFn w).card
      have hcnt_le : cnt ≤ 2 ^ k := le_trans (Finset.card_filter_le _ _) (by simp)
      have hcnt_lt : cnt < 2 ^ L := lt_of_le_of_lt hcnt_le (Nat.pow_lt_pow_right (by omega) (by dsimp [L]; omega))
      have hcnt_split : dpPrefixCount p n d hd (k - 1) locFn yFn (fun _ => false) +
          dpPrefixCount p n d hd (k - 1) locFn yFn (Function.update (fun _ => false) (k - 1) true) = cnt := by
        rw [dpPrefixCount_spec p n d hp hd hdn (k - 1) (by omega),
          dpPrefixCount_spec p n d hp hd hdn (k - 1) (by omega)]
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext w
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
          · intro h
            cases hbit : w.val.testBit (k - 1)
            · left; refine ⟨fun pos hlo hhi => ?_, h⟩
              have heq : pos = k - 1 := by omega
              rw [heq, hbit]
            · right; refine ⟨fun pos hlo hhi => ?_, h⟩
              have heq : pos = k - 1 := by omega
              rw [heq, Function.update_self, hbit]
        · rw [Finset.disjoint_left]; intro w hw0 hw1
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw0 hw1
          have h0 := hw0.1 (k - 1) le_rfl (by omega)
          have h1 := hw1.1 (k - 1) le_rfl (by omega)
          rw [Function.update_self] at h1
          rw [h0] at h1; exact Bool.false_ne_true h1
      have hcntBv_ev : bvVal s7 x cntBv = cnt := by
        rw [h7.2.2.2.2 x hx, bvVal_ext h6.1 x hx c0Top h5.2.2.1, h5.2.2.2.2 x hx, h6.2.2.2.2 x hx]
        have hloc4 : (fun i v b => s4.weval x (locW i v b)) = locFn :=
          funext fun i => funext fun v => funext fun b => by
            rw [CState.ext_weval h24 x hx _ (h2.2.2.1 i v b), hloc_ev]
        have hloc5 : (fun i v b => s5.weval x (locW i v b)) = locFn :=
          funext fun i => funext fun v => funext fun b => by
            rw [CState.ext_weval h25 x hx _ (h2.2.2.1 i v b), hloc_ev]
        have hy4 : (fun i => s4.weval x (yW i)) = yFn :=
          funext fun i => by rw [CState.ext_weval h04 x hx _ (hy_lt i), hev_y i]
        have hy5 : (fun i => s5.weval x (yW i)) = yFn :=
          funext fun i => by rw [CState.ext_weval h05 x hx _ (hy_lt i), hev_y i]
        have hp4 : (fun _ : ℕ => s4.weval x w0) = (fun _ => false) :=
          funext fun _ => by rw [CState.ext_weval h4.1 x hx w0 h3.2.2.1, h3.2.2.2.2 x hx]
        have hp5 : (fun pos => s5.weval x (Function.update (fun _ => w0) (k - 1) w1 pos)) =
            Function.update (fun _ => false) (k - 1) true :=
          funext fun pos => by
            by_cases heq : pos = k - 1
            · rw [heq, Function.update_self, Function.update_self, CState.ext_weval h5.1 x hx w1 h4.2.2.1, h4.2.2.2.2 x hx]
            · rw [Function.update_of_ne heq, Function.update_of_ne heq,
                CState.ext_weval (CState.ext_trans h4.1 h5.1) x hx w0 h3.2.2.1, h3.2.2.2.2 x hx]
        rw [hloc4, hloc5, hy4, hy5, hp4, hp5, ← Nat.add_mod, hcnt_split, Nat.mod_eq_of_lt hcnt_lt]

      have hcard_cnt : Nat.card {w : Fin (2 ^ k) //
          letI : ∀ P : Prop, Decidable P := Classical.propDecidable
          ∀ i : Fin n, (List.finRange p).foldl (fun b a =>
            xor b (((List.finRange r).foldl (fun z jj =>
              stepOp k (z ^^^ rotOp k (if bank i then 2 else 1) z ^^^ rotOp k (k - if bank i then 2 else 1) z) ^^^
                rotOp k (if bank i then 3 * (jj.val + 1) + 1 else 2 * jj.val) w.val ^^^
                tileOp p n ((if bank i then cc else cr) jj).val)
              (rotOp k (if bank i then 3 else 1) w.val ^^^ tileOp p n (if bank i then nc.val else nr.val))).testBit
              ((a.val * n + i.val + if bank i then 3 * r + 1 else 2 * r - 2) % k))) false = y.val.testBit i.val} = cnt := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        apply congrArg Finset.card; apply Finset.filter_congr; intro w _
        exact hhit_iff w

      rw [h13.2.2.2.2 x hx, CState.ext_weval h012 x hx modeW hmode_lt, hev_mode]
      cases countMode
      ·
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [h12.2.2.2.2 x hx, CState.ext_weval h911 x hx tLtCntW h9.2.2.1, h9.2.2.2.2 x hx,
          bvVal_ext h08 x hx tBv ht_lt, ht_bv, bvVal_ext h8.1 x hx cntBv h7.2.2.1, hcntBv_ev,
          h11.2.2.2.2 x hx j (by rw [bvVal_ext h010 x hx jBv hj_lt, hj_bv])]
        have hloc7 : (fun i v b => s7.weval x (locW i v b)) = locFn :=
          funext fun i => funext fun v => funext fun b => by
            rw [CState.ext_weval h27 x hx _ (h2.2.2.1 i v b), hloc_ev]
        have hy7 : (fun i => s7.weval x (yW i)) = yFn :=
          funext fun i => by rw [CState.ext_weval h07 x hx _ (hy_lt i), hev_y i]
        have hp7 : (fun _ : ℕ => s7.weval x w0) = (fun _ => false) :=
          funext fun _ => by rw [CState.ext_weval (CState.ext_trans h4.1 h47) x hx w0 h3.2.2.1, h3.2.2.2.2 x hx]
        have hunr := h8.2.2.2.2.2 x hx
        rw [bvVal_ext h07 x hx tBv ht_lt, ht_bv, hloc7, hy7, hp7] at hunr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨hlt_t, hbit_j⟩
          let cntFn := fun m' pf => dpPrefixCount p n d hd m' locFn yFn pf
          have hspec := unrankLoop_spec k (hitLoc p n d locFn yFn) cntFn
            (fun m' hm' pf => by
              dsimp only [cntFn]; rw [dpPrefixCount_spec p n d hp hd hdn m' hm' locFn yFn pf]
              exact card_filter_eq_of_iff _ _ _ fun _ _ => Iff.rfl)
            k le_rfl t.val (fun _ => false) (lt_of_lt_of_eq hlt_t (by
              dsimp only [cnt]
              exact card_filter_eq_of_iff _ _ _ fun _ _ => ⟨fun h => ⟨fun _ hlo hhi => by omega, h⟩, fun h => h.2⟩))
          set w : Fin (2 ^ k) := bitsToFin k (unrankLoop k cntFn k (t.val, fun _ => false)).2
          refine ⟨w, (hhit_iff w).mpr hspec.2.1, ?_, ?_⟩
          · rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hspec.2.2]
            exact card_filter_eq_of_iff _ _ _ fun z _ =>
              ⟨fun ⟨h1', h2'⟩ => ⟨h1', fun _ hlo hhi => by omega, (hhit_iff z).mp h2'⟩,
               fun ⟨h1', _, h2'⟩ => ⟨h1', (hhit_iff z).mpr h2'⟩⟩
          · by_cases hj0 : j.val = 0
            · exact Or.inl hj0
            · right
              have hjlt : j.val - 1 < k := by have := j.isLt; omega
              rw [bitsToFin_testBit k _ (j.val - 1) hjlt]
              rw [if_neg hj0, CState.ext_weval h810 x hx (prefEnd (j.val - 1)) (h8.2.2.2.1 _ hjlt),
                hunr.2 (j.val - 1) hjlt] at hbit_j
              exact hbit_j
        · rintro ⟨w, hhit_w, hrank_w, hj_w⟩
          have hhit_loc_w : hitLoc p n d locFn yFn w := (hhit_iff w).mp hhit_w
          have hrank_fin : (Finset.univ.filter fun z : Fin (2 ^ k) => z < w ∧ hitLoc p n d locFn yFn z).card = t.val := by
            rw [← hrank_w, Nat.card_eq_fintype_card, Fintype.card_subtype]
            apply congrArg Finset.card; apply Finset.filter_congr; intro z _
            exact and_congr_right fun _ => (hhit_iff z).symm
          have hlt_t : t.val < cnt := by
            rw [← hrank_fin]
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨fun z hz => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢; exact hz.2, ?_⟩
            intro heq
            have hw_in : w ∈ Finset.univ.filter (fun z : Fin (2 ^ k) => hitLoc p n d locFn yFn z) := by
              simp [hhit_loc_w]
            rw [← heq] at hw_in
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw_in
            exact lt_irrefl w hw_in.1
          refine ⟨hlt_t, ?_⟩
          by_cases hj0 : j.val = 0
          · rw [if_pos hj0, CState.ext_weval h410 x hx w1 h4.2.2.1, h4.2.2.2.2 x hx]
          · rw [if_neg hj0]
            have hjlt : j.val - 1 < k := by have := j.isLt; omega
            rw [CState.ext_weval h810 x hx (prefEnd (j.val - 1)) (h8.2.2.2.1 _ hjlt), hunr.2 (j.val - 1) hjlt]
            let cntFn := fun m' pf => dpPrefixCount p n d hd m' locFn yFn pf
            have hspec := unrankLoop_spec k (hitLoc p n d locFn yFn) cntFn
              (fun m' hm' pf => by
                dsimp only [cntFn]; rw [dpPrefixCount_spec p n d hp hd hdn m' hm' locFn yFn pf]
                exact card_filter_eq_of_iff _ _ _ fun _ _ => Iff.rfl)
              k le_rfl t.val (fun _ => false) (lt_of_lt_of_eq hlt_t (by
                dsimp only [cnt]
                exact card_filter_eq_of_iff _ _ _ fun _ _ => ⟨fun h => ⟨fun _ hlo hhi => by omega, h⟩, fun h => h.2⟩))
            set w' : Fin (2 ^ k) := bitsToFin k (unrankLoop k cntFn k (t.val, fun _ => false)).2
            have hrank_w' : (Finset.univ.filter fun z : Fin (2 ^ k) => z < w' ∧ hitLoc p n d locFn yFn z).card = t.val := by
              rw [← hspec.2.2]
              exact card_filter_eq_of_iff _ _ _ fun z _ =>
                ⟨fun ⟨h1', h2'⟩ => ⟨h1', fun _ hlo hhi => by omega, h2'⟩, fun ⟨h1', _, h2'⟩ => ⟨h1', h2'⟩⟩
            have hww' : w = w' := by
              rcases lt_trichotomy w w' with hlt | heq | hgt
              · exfalso
                have hlt_c : (Finset.univ.filter fun z : Fin (2 ^ k) => z < w ∧ hitLoc p n d locFn yFn z).card <
                    (Finset.univ.filter fun z : Fin (2 ^ k) => z < w' ∧ hitLoc p n d locFn yFn z).card := by
                  apply Finset.card_lt_card; rw [Finset.ssubset_iff_subset_ne]
                  refine ⟨fun z hz => by
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
                    exact ⟨lt_trans hz.1 hlt, hz.2⟩, ?_⟩
                  intro heq'
                  have hw_in : w ∈ Finset.univ.filter (fun z : Fin (2 ^ k) => z < w' ∧ hitLoc p n d locFn yFn z) := by
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hlt, hhit_loc_w⟩
                  rw [← heq'] at hw_in; simp at hw_in
                omega
              · exact heq
              · exfalso
                have hlt_c : (Finset.univ.filter fun z : Fin (2 ^ k) => z < w' ∧ hitLoc p n d locFn yFn z).card <
                    (Finset.univ.filter fun z : Fin (2 ^ k) => z < w ∧ hitLoc p n d locFn yFn z).card := by
                  apply Finset.card_lt_card; rw [Finset.ssubset_iff_subset_ne]
                  refine ⟨fun z hz => by
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
                    exact ⟨lt_trans hz.1 hgt, hz.2⟩, ?_⟩
                  intro heq'
                  have hw'_in : w' ∈ Finset.univ.filter (fun z : Fin (2 ^ k) => z < w ∧ hitLoc p n d locFn yFn z) := by
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hgt, hspec.2.1⟩
                  rw [← heq'] at hw'_in; simp at hw'_in
                omega
            have hbit_eq : (unrankLoop k cntFn k (t.val, fun _ => false)).2 (j.val - 1) = w'.val.testBit (j.val - 1) :=
              (bitsToFin_testBit k _ (j.val - 1) hjlt).symm
            rw [hbit_eq, ← hww']
            exact hj_w.resolve_left hj0
      ·
        simp only [↓reduceIte]
        rw [CState.ext_weval h1012 x hx cntBitW h10.2.2.1,
          h10.2.2.2.2 x hx j (by rw [bvVal_ext h09 x hx jBv hj_lt, hj_bv]),
          CState.ext_weval h79 x hx (cntBv j) (h7.2.2.1 j),
          ← bvVal_testBit s7 x cntBv j, hcntBv_ev]
        dsimp only [stepOp, rotOp, tileOp] at hcard_cnt
        rw [hcard_cnt]
    · exact ⟨fun ⟨hv, _⟩ => False.elim (hval hv),
        fun ⟨hv, _⟩ => False.elim (hval fun i => by rw [← hreach_eq]; exact hv i)⟩
