import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21437_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

inductive T where
  | leaf : ℕ → T
  | node : ℕ → Bool → T → T → T

namespace T

def ev (v : ℕ → Bool) : T → Bool
  | leaf i => v i
  | node _ a l r => if a then (ev v l && ev v r) else (ev v l || ev v r)

def lc (u : ℕ) : T → ℕ
  | leaf i => if i = u then 1 else 0
  | node _ _ l r => lc u l + lc u r

def gc (j : ℕ) : T → ℕ
  | leaf _ => 0
  | node k _ l r => (if k = j then 1 else 0) + gc j l + gc j r

def sz : T → ℕ
  | leaf _ => 0
  | node _ _ l r => sz l + sz r + 1

def bel (m : ℕ) : T → Prop
  | leaf i => i < m
  | node _ _ l r => bel m l ∧ bel m r

end T

theorem ev_congr (t : T) (m : ℕ) (hb : t.bel m) (v v' : ℕ → Bool) (h : ∀ i < m, v i = v' i) :
    t.ev v = t.ev v' := by
  induction t with
  | leaf i => exact h i hb
  | node j a l r ihl ihr => simp only [T.ev, ihl hb.1, ihr hb.2]

theorem below_of (m : ℕ) (t : T) (h : ∀ u, t.lc u ≠ 0 → u < m) : t.bel m := by
  induction t with
  | leaf i => exact h i (by simp [T.lc])
  | node j a l r ihl ihr =>
    exact ⟨ihl fun u hu => h u (by simp only [T.lc]; omega),
      ihr fun u hu => h u (by simp only [T.lc]; omega)⟩

def gop (a : Bool) : GateOp := if a then GateOp.and else GateOp.or

def co (m : ℕ) (t : T) (k : ℕ) : ℕ :=
  match t with
  | T.leaf i => i
  | T.node _ _ l r => m + k + l.sz + r.sz

theorem co_nd (m j : ℕ) (a : Bool) (l r : T) (k : ℕ) :
    co m (T.node j a l r) k = m + k + l.sz + r.sz := rfl

theorem co_lf (m i k : ℕ) : co m (T.leaf i) k = i := rfl

def cg (m : ℕ) : T → ℕ → List Gate
  | T.leaf _, _ => []
  | T.node _ a l r, k =>
    cg m l k ++ cg m r (k + l.sz) ++ [⟨gop a, [co m l k, co m r (k + l.sz)]⟩]

theorem cg_len (m : ℕ) (t : T) : ∀ k, (cg m t k).length = t.sz := by
  induction t with
  | leaf i => intro k; simp [cg, T.sz]
  | node j a l r ihl ihr => intro k; simp only [cg, T.sz, List.length_append, List.length_cons, List.length_nil, ihl, ihr]

theorem co_lt (m : ℕ) (t : T) (k : ℕ) (h : t.bel m) : co m t k < m + k + t.sz := by
  cases t with
  | leaf i => simp only [co, T.sz, T.bel] at *; omega
  | node j a l r => simp only [co, T.sz]; omega

theorem co_node (m : ℕ) (t : T) (k : ℕ) (h : 0 < t.sz) : co m t k + 1 = m + k + t.sz := by
  cases t with
  | leaf i => simp [T.sz] at h
  | node j a l r => simp only [co, T.sz]; omega

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (w : List Bool) (x : Bool) (i : ℕ) :
    (w ++ [x]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then x else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : 1 ≤ i - w.length := by omega
    rw [List.getElem?_eq_none (by simpa using this)]; rfl

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem fold_stab (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step, getD_snoc, if_pos h]

theorem wire_val (gs : List Gate) : ∀ (w0 : List Bool) (j : ℕ), j < gs.length →
    (∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w0.length + j) →
    (gs.foldl step w0).getD (w0.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i => (gs.foldl step w0).getD i false) := by
  induction gs with
  | nil => intro w0 j hj; simp at hj
  | cons g gs ih =>
    intro w0 j hj hin
    cases j with
    | zero =>
      simp only [List.getD_cons_zero, List.foldl_cons, Nat.add_zero] at *
      rw [fold_stab _ _ _ (by simp [step])]
      have e : (step w0 g).getD w0.length false =
          g.op.eval (g.inputs.map fun i => w0.getD i false) := by
        simp [step]
      rw [e]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi' := hin i hi
      rw [fold_stab _ _ _ (by simp [step]; omega)]
      show _ = (w0 ++ [_]).getD i false
      rw [getD_snoc, if_pos hi']
    | succ j =>
      simp only [List.getD_cons_succ, List.foldl_cons] at *
      have h2 := ih (step w0 g) j (by simpa using hj)
        (by intro i hi; have := hin i hi; simp [step]; omega)
      rw [show w0.length + (j + 1) = (step w0 g).length + j by simp [step]; omega]
      exact h2

theorem cg_sem (m : ℕ) (t : T) : ∀ (k : ℕ) (w : List Bool), w.length = m + k → t.bel m →
    ((cg m t k).foldl step w).getD (co m t k) false = t.ev (fun i => w.getD i false) := by
  induction t with
  | leaf i => intro k w hw hb; simp [cg, co, T.ev]
  | node j a l r ihl ihr =>
    intro k w hw hb
    obtain ⟨hbl, hbr⟩ := hb
    have l1 : ((cg m l k).foldl step w).length = m + (k + l.sz) := by
      rw [fold_len, hw, cg_len]; omega
    have l2 : ((cg m r (k + l.sz)).foldl step ((cg m l k).foldl step w)).length
        = m + k + l.sz + r.sz := by
      rw [fold_len, l1, cg_len]; omega
    have e1 := ihl k w hw hbl
    have e2 := ihr (k + l.sz) _ l1 hbr
    have e1' : ((cg m r (k + l.sz)).foldl step ((cg m l k).foldl step w)).getD (co m l k) false
        = l.ev (fun i => w.getD i false) := by
      rw [fold_stab _ _ _ (by have := co_lt m l k hbl; omega), e1]
    have e2' : r.ev (fun i => ((cg m l k).foldl step w).getD i false)
        = r.ev (fun i => w.getD i false) := by
      apply ev_congr r m hbr
      intro i hi
      rw [fold_stab _ _ _ (by omega)]
    simp only [cg, List.foldl_append, List.foldl_cons, List.foldl_nil]
    show (_ ++ [_]).getD (co m (T.node j a l r) k) false = _
    rw [co_nd, getD_snoc, if_neg (by omega), if_pos (by omega)]
    simp only [List.map_cons, List.map_nil, e1', e2, e2', T.ev, gop]
    cases a <;> simp [GateOp.eval]

theorem cg_ops (m : ℕ) (t : T) : ∀ k, ∀ g ∈ cg m t k,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  induction t with
  | leaf i => intro k g hg; simp [cg] at hg
  | node j a l r ihl ihr =>
    intro k g hg
    simp only [cg, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ihl _ g hg
    · exact ihr _ g hg
    · subst hg; cases a <;> simp [gop]

def RB (m : ℕ) : ℕ → List Gate → Prop
  | _, [] => True
  | k, g :: gs => (∀ i ∈ g.inputs, i < m + k) ∧ RB m (k + 1) gs

theorem RB_append (m : ℕ) (a b : List Gate) : ∀ k,
    RB m k (a ++ b) ↔ RB m k a ∧ RB m (k + a.length) b := by
  induction a with
  | nil => intro k; simp [RB]
  | cons g gs ih =>
    intro k
    simp only [List.cons_append, RB, ih, List.length_cons, and_assoc]
    rw [show k + 1 + gs.length = k + (gs.length + 1) by omega]

theorem cg_RB (m : ℕ) (t : T) : ∀ k, t.bel m → RB m k (cg m t k) := by
  induction t with
  | leaf i => intro k hb; simp [cg, RB]
  | node j a l r ihl ihr =>
    intro k hb
    simp only [cg, RB_append, cg_len, List.length_append]
    refine ⟨⟨ihl k hb.1, ihr _ hb.2⟩, ?_, trivial⟩
    intro i hi
    have h1 := co_lt m l k hb.1
    have h2 := co_lt m r (k + l.sz) hb.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega

theorem RB_get (m : ℕ) (gs : List Gate) : ∀ (k : ℕ), RB m k gs → ∀ j, j < gs.length →
    ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < m + k + j := by
  induction gs with
  | nil => intro k h j hj; simp at hj
  | cons g gs ih =>
    intro k h j hj i hi
    cases j with
    | zero => simpa using h.1 i (by simpa using hi)
    | succ j =>
      have := ih (k + 1) h.2 j (by simpa using hj) i (by simpa using hi)
      omega

def cnt (u : ℕ) (gs : List Gate) : ℕ := (gs.map fun g => g.inputs.count u).sum

theorem cnt_append (u : ℕ) (a b : List Gate) : cnt u (a ++ b) = cnt u a + cnt u b := by
  simp [cnt]

theorem readsIn_eq (F : Circuit) (u : ℕ) : readsIn F (Finset.range F.size) u = cnt u F.gates := by
  unfold readsIn gateAt Circuit.size cnt
  generalize F.gates = gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons, ih]
    omega

theorem cnt_low (m : ℕ) (t : T) (u : ℕ) (hu : u < m) : ∀ k,
    cnt u (cg m t k) + (if co m t k = u then 1 else 0) = t.lc u := by
  induction t with
  | leaf i =>
    intro k
    show 0 + (if i = u then 1 else 0) = (if i = u then 1 else 0)
    omega
  | node j a l r ihl ihr =>
    intro k
    have h1 := ihl k
    have h2 := ihr (k + l.sz)
    have e : cnt u [(⟨gop a, [co m l k, co m r (k + l.sz)]⟩ : Gate)] =
        (if co m l k = u then 1 else 0) + (if co m r (k + l.sz) = u then 1 else 0) := by
      simp only [cnt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.count_cons, List.count_nil]
      split_ifs <;> simp_all
    have e3 : (if co m (T.node j a l r) k = u then 1 else 0) = 0 :=
      if_neg (by rw [co_nd]; omega)
    simp only [cg, cnt_append, e, T.lc, e3]
    omega

theorem arith (k j a b A B X Y m : ℕ)
    (h1 : X + A = if k ≤ j ∧ j < k + a then 1 else 0)
    (h2 : Y + B = if k + a ≤ j ∧ j < k + a + b then 1 else 0) :
    X + Y + (A + B) + (if m + k + a + b = m + j then 1 else 0) =
      if k ≤ j ∧ j < k + (a + b + 1) then 1 else 0 := by
  by_cases p1 : k ≤ j ∧ j < k + a
  · rw [if_pos p1] at h1
    rw [if_neg (by omega)] at h2
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  · rw [if_neg p1] at h1
    by_cases p2 : k + a ≤ j ∧ j < k + a + b
    · rw [if_pos p2] at h2
      rw [if_neg (by omega), if_pos (by omega)]
      omega
    · rw [if_neg p2] at h2
      by_cases p3 : m + k + a + b = m + j
      · rw [if_pos p3, if_pos (by omega)]
        omega
      · rw [if_neg p3, if_neg (by omega)]
        omega

theorem cnt_high (m : ℕ) (t : T) (j : ℕ) : ∀ k, t.bel m →
    cnt (m + j) (cg m t k) + (if co m t k = m + j then 1 else 0) =
      if k ≤ j ∧ j < k + t.sz then 1 else 0 := by
  induction t with
  | leaf i =>
    intro k hb
    simp only [T.bel] at hb
    have h1 : (if co m (T.leaf i) k = m + j then 1 else 0) = 0 :=
      if_neg (by rw [co_lf]; omega)
    have h2 : (if k ≤ j ∧ j < k + (T.leaf i).sz then 1 else 0) = 0 :=
      if_neg (by simp only [T.sz]; omega)
    rw [h1, h2]
    simp [cg, cnt]
  | node j' a l r ihl ihr =>
    intro k hb
    have h1 := ihl k hb.1
    have h2 := ihr (k + l.sz) hb.2
    have e : cnt (m + j) [(⟨gop a, [co m l k, co m r (k + l.sz)]⟩ : Gate)] =
        (if co m l k = m + j then 1 else 0) + (if co m r (k + l.sz) = m + j then 1 else 0) := by
      simp only [cnt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.count_cons, List.count_nil]
      split_ifs <;> simp_all
    simp only [cg, cnt_append, e, T.sz, co_nd]
    exact arith k j l.sz r.sz _ _ _ _ m h1 h2

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def form (m : ℕ) (C : Circuit) (Rg : Finset ℕ) : ℕ → ℕ → T
  | 0, w => T.leaf w
  | f + 1, w =>
    if m ≤ w ∧ w - m ∈ Rg then
      T.node (w - m) (isAnd (gateAt C (w - m)).op)
        (form m C Rg f ((gateAt C (w - m)).inputs.getD 0 0))
        (form m C Rg f ((gateAt C (w - m)).inputs.getD 1 0))
    else T.leaf w

structure Reg (m : ℕ) (C : Circuit) (S Rg : Finset ℕ) (tj bw : ℕ) : Prop where
  rb : ReadsBack m C
  tj_mem : tj ∈ Rg
  lt : ∀ j ∈ Rg, j < C.size
  Slt : ∀ i ∈ S, i < m
  card : 2 ≤ S.card
  gate : ∀ j ∈ Rg,
    (((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (gateAt C j).inputs.length = 2) ∧
    ∀ w ∈ (gateAt C j).inputs, w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg) ∨ w = bw
  bwS : bw ∉ S
  bwR : ¬ (m ≤ bw ∧ bw - m ∈ Rg)
  bw1 : readsIn C Rg bw ≤ 1
  sread : ∀ i ∈ S, readsIn C (Finset.range C.size) i = 1 ∧ readsIn C Rg i = 1
  rread : ∀ j ∈ Rg, readsIn C Rg (m + j) = if j = tj then 0 else 1
  rtot : ∀ j ∈ Rg, j ≠ tj → readsIn C (Finset.range C.size) (m + j) = 1
  orp : ∀ j ∈ Rg,
    Relation.TransGen (fun a c => m ≤ c ∧ c - m ∈ Rg ∧ a ∈ (gateAt C (c - m)).inputs) bw (m + j) →
    (gateAt C j).op = GateOp.or

section
variable {m : ℕ} {C : Circuit} {S Rg : Finset ℕ} {tj bw : ℕ}

theorem inp (h : Reg m C S Rg tj bw) (j : ℕ) (hj : j ∈ Rg) :
    ∃ i0 i1, (gateAt C j).inputs = [i0, i1] ∧ i0 < m + j ∧ i1 < m + j := by
  obtain ⟨i0, i1, hi⟩ := List.length_eq_two.mp (h.gate j hj).1.2
  refine ⟨i0, i1, hi, ?_, ?_⟩
  · exact h.rb j (h.lt j hj) i0 (by rw [hi]; simp)
  · exact h.rb j (h.lt j hj) i1 (by rw [hi]; simp)

theorem form_leaf (f w : ℕ) (hw : ¬ (m ≤ w ∧ w - m ∈ Rg)) : form m C Rg f w = T.leaf w := by
  cases f with
  | zero => rfl
  | succ f => simp only [form, if_neg hw]

theorem form_gate (f j : ℕ) (hj : j ∈ Rg) (i0 i1 : ℕ) (hi : (gateAt C j).inputs = [i0, i1]) :
    form m C Rg (f + 1) (m + j) =
      T.node j (isAnd (gateAt C j).op) (form m C Rg f i0) (form m C Rg f i1) := by
  have e : m + j - m = j := by omega
  simp only [form, e, hi]
  rw [if_pos ⟨by omega, hj⟩]
  rfl

theorem form_ind (h : Reg m C S Rg tj bw) (P : ℕ → T → Prop)
    (hleaf : ∀ w, ¬ (m ≤ w ∧ w - m ∈ Rg) → P w (T.leaf w))
    (hnode : ∀ j ∈ Rg, ∀ i0 i1 t0 t1, (gateAt C j).inputs = [i0, i1] → i0 < m + j → i1 < m + j →
      P i0 t0 → P i1 t1 → P (m + j) (T.node j (isAnd (gateAt C j).op) t0 t1)) :
    ∀ f w, w < f → P w (form m C Rg f w) := by
  intro f
  induction f with
  | zero => intro w hw; omega
  | succ f ih =>
    intro w hw
    by_cases hc : m ≤ w ∧ w - m ∈ Rg
    · obtain ⟨hmw, hj⟩ := hc
      obtain ⟨j, rfl⟩ : ∃ j, w = m + j := ⟨w - m, by omega⟩
      have e : m + j - m = j := by omega
      rw [e] at hj
      obtain ⟨i0, i1, hi, h0, h1⟩ := inp h j hj
      rw [form_gate f j hj i0 i1 hi]
      exact hnode j hj i0 i1 _ _ hi h0 h1 (ih i0 (by omega)) (ih i1 (by omega))
    · rw [form_leaf _ _ hc]
      exact hleaf w hc

theorem form_ev (h : Reg m C S Rg tj bw) (x : List Bool) (hx : x.length = m) :
    ∀ f w, w < f →
      (form m C Rg f w).ev (fun i => (C.wires x).getD i false) = (C.wires x).getD w false := by
  apply form_ind h (fun w t => t.ev (fun i => (C.wires x).getD i false) = (C.wires x).getD w false)
  · intro w _; rfl
  · intro j hj i0 i1 t0 t1 hi h0 h1 e0 e1
    have hv := wire_val C.gates x j (h.lt j hj)
      (by intro i hi'; rw [hx]; exact h.rb j (h.lt j hj) i hi')
    rw [hx] at hv
    have hi' : (C.gates.getD j ⟨GateOp.or, []⟩).inputs = [i0, i1] := hi
    rw [wires_eq] at e0 e1 ⊢
    rw [hv, hi']
    rcases (h.gate j hj).1.1 with hop | hop
    · have hop' : (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.and := hop
      simp only [T.ev, hop, hop', isAnd, e0, e1, GateOp.eval, List.map_cons, List.map_nil]
      simp
    · have hop' : (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.or := hop
      simp only [T.ev, hop, hop', isAnd, e0, e1, GateOp.eval, List.map_cons, List.map_nil]
      simp

theorem form_noR (h : Reg m C S Rg tj bw) :
    ∀ f w, w < f → ∀ u, (m ≤ u ∧ u - m ∈ Rg) → (form m C Rg f w).lc u = 0 := by
  apply form_ind h (fun w t => ∀ u, (m ≤ u ∧ u - m ∈ Rg) → t.lc u = 0)
  · intro w hw u hu
    simp only [T.lc]
    rw [if_neg]
    rintro rfl
    exact hw hu
  · intro j hj i0 i1 t0 t1 hi h0 h1 e0 e1 u hu
    simp only [T.lc, e0 u hu, e1 u hu]

theorem form_ident (h : Reg m C S Rg tj bw) :
    ∀ f w, w < f → ∀ u,
      (if w = u then 1 else 0) + ∑ j ∈ Rg, (form m C Rg f w).gc j * (gateAt C j).inputs.count u =
        (form m C Rg f w).lc u +
          (if m ≤ u ∧ u - m ∈ Rg then (form m C Rg f w).gc (u - m) else 0) := by
  apply form_ind h (fun w t => ∀ u,
      (if w = u then 1 else 0) + ∑ j ∈ Rg, t.gc j * (gateAt C j).inputs.count u =
        t.lc u + (if m ≤ u ∧ u - m ∈ Rg then t.gc (u - m) else 0))
  · intro w hw u
    simp [T.gc, T.lc]
  · intro j hj i0 i1 t0 t1 hi h0 h1 e0 e1 u
    have a0 := e0 u
    have a1 := e1 u
    have es : ∑ q ∈ Rg, (T.node j (isAnd (gateAt C j).op) t0 t1).gc q * (gateAt C q).inputs.count u
        = (gateAt C j).inputs.count u + ∑ q ∈ Rg, t0.gc q * (gateAt C q).inputs.count u
          + ∑ q ∈ Rg, t1.gc q * (gateAt C q).inputs.count u := by
      simp only [T.gc, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, hj, if_true]
    have ec : (gateAt C j).inputs.count u = (if i0 = u then 1 else 0) + (if i1 = u then 1 else 0) := by
      rw [hi]
      simp only [List.count_cons, List.count_nil]
      split_ifs <;> simp_all
    rw [es, ec]
    simp only [T.lc, T.gc]
    by_cases hc : m ≤ u ∧ u - m ∈ Rg
    · rw [if_pos hc] at a0 a1
      rw [if_pos hc]
      by_cases hu : m + j = u
      · have k1 : (if m + j = u then 1 else 0) = 1 := if_pos hu
        have k2 : (if j = u - m then 1 else 0) = 1 := if_pos (by omega)
        rw [k1, k2]
        omega
      · have k1 : (if m + j = u then 1 else 0) = 0 := if_neg hu
        have k2 : (if j = u - m then 1 else 0) = 0 := if_neg (by omega)
        rw [k1, k2]
        omega
    · rw [if_neg hc] at a0 a1
      rw [if_neg hc]
      have hu : m + j ≠ u := by
        rintro rfl
        exact hc ⟨by omega, by rw [show m + j - m = j by omega]; exact hj⟩
      have k1 : (if m + j = u then 1 else 0) = 0 := if_neg hu
      rw [k1]
      omega

def OrPath (bw : ℕ) : T → Prop
  | T.leaf _ => True
  | T.node _ a l r => (l.lc bw + r.lc bw ≠ 0 → a = false) ∧ OrPath bw l ∧ OrPath bw r

theorem form_or (h : Reg m C S Rg tj bw) :
    ∀ f w, w < f →
      ((form m C Rg f w).lc bw ≠ 0 → w = bw ∨
        Relation.TransGen (fun a c => m ≤ c ∧ c - m ∈ Rg ∧ a ∈ (gateAt C (c - m)).inputs) bw w) ∧
      OrPath bw (form m C Rg f w) := by
  apply form_ind h (fun w t => (t.lc bw ≠ 0 → w = bw ∨
        Relation.TransGen (fun a c => m ≤ c ∧ c - m ∈ Rg ∧ a ∈ (gateAt C (c - m)).inputs) bw w) ∧
      OrPath bw t)
  · intro w hw
    refine ⟨?_, trivial⟩
    intro hne
    left
    by_contra hwb
    exact hne (by simp only [T.lc]; rw [if_neg hwb])
  · intro j hj i0 i1 t0 t1 hi h0 h1 e0 e1
    have e : m + j - m = j := by omega
    have reach : (T.node j (isAnd (gateAt C j).op) t0 t1).lc bw ≠ 0 →
        Relation.TransGen (fun a c => m ≤ c ∧ c - m ∈ Rg ∧ a ∈ (gateAt C (c - m)).inputs)
          bw (m + j) := by
      intro hne
      simp only [T.lc] at hne
      have s0 : (fun a c => m ≤ c ∧ c - m ∈ Rg ∧ a ∈ (gateAt C (c - m)).inputs) i0 (m + j) :=
        ⟨by omega, by rw [e]; exact hj, by rw [e, hi]; simp⟩
      have s1 : (fun a c => m ≤ c ∧ c - m ∈ Rg ∧ a ∈ (gateAt C (c - m)).inputs) i1 (m + j) :=
        ⟨by omega, by rw [e]; exact hj, by rw [e, hi]; simp⟩
      by_cases c0 : t0.lc bw ≠ 0
      · rcases e0.1 c0 with rfl | ht
        · exact Relation.TransGen.single s0
        · exact Relation.TransGen.tail ht s0
      · have c1 : t1.lc bw ≠ 0 := by omega
        rcases e1.1 c1 with rfl | ht
        · exact Relation.TransGen.single s1
        · exact Relation.TransGen.tail ht s1
    refine ⟨fun hne => Or.inr (reach hne), ?_, e0.2, e1.2⟩
    intro hne
    have hop := h.orp j hj (reach (by simpa only [T.lc] using hne))
    rw [hop]
    rfl

theorem rem (bw : ℕ) (t : T) : t.lc bw = 1 → OrPath bw t →
    t = T.leaf bw ∨ ∃ t' : T, (∀ u, t'.lc u = if u = bw then 0 else t.lc u) ∧
      ∀ v : ℕ → Bool, t.ev v = (v bw || t'.ev v) := by
  induction t with
  | leaf i =>
    intro h1 _
    left
    simp only [T.lc] at h1
    by_cases hi : i = bw
    · rw [hi]
    · rw [if_neg hi] at h1; omega
  | node k a l r ihl ihr =>
    intro h1 hop
    right
    simp only [T.lc] at h1
    obtain ⟨ha, hl, hr⟩ := hop
    have ha' : a = false := ha (by omega)
    subst ha'
    rcases (by omega : (l.lc bw = 1 ∧ r.lc bw = 0) ∨ (l.lc bw = 0 ∧ r.lc bw = 1)) with ⟨c1, c0⟩ | ⟨c0, c1⟩
    · rcases ihl c1 hl with rfl | ⟨l', hl1, hl2⟩
      · refine ⟨r, ?_, ?_⟩
        · intro u
          by_cases hu : u = bw
          · rw [if_pos hu, hu, c0]
          · rw [if_neg hu]
            simp only [T.lc]
            rw [if_neg (fun hh => hu hh.symm)]
            omega
        · intro v; simp [T.ev]
      · refine ⟨T.node k false l' r, ?_, ?_⟩
        · intro u
          simp only [T.lc, hl1 u]
          by_cases hu : u = bw
          · rw [if_pos hu, if_pos hu, hu, c0]
          · rw [if_neg hu, if_neg hu]
        · intro v; simp [T.ev, hl2 v, Bool.or_assoc]
    · rcases ihr c1 hr with rfl | ⟨r', hr1, hr2⟩
      · refine ⟨l, ?_, ?_⟩
        · intro u
          by_cases hu : u = bw
          · rw [if_pos hu, hu, c0]
          · rw [if_neg hu]
            simp only [T.lc]
            rw [if_neg (fun hh => hu hh.symm)]
            omega
        · intro v; simp [T.ev, Bool.or_comm]
      · refine ⟨T.node k false l r', ?_, ?_⟩
        · intro u
          simp only [T.lc, hr1 u]
          by_cases hu : u = bw
          · rw [if_pos hu, if_pos hu, hu, c0]
          · rw [if_neg hu, if_neg hu]
        · intro v; simp [T.ev, hr2 v, Bool.or_left_comm]

theorem tj_max (h : Reg m C S Rg tj bw) : ∀ j ∈ Rg, j ≤ tj := by
  have key : ∀ j ∈ Rg, j ≠ tj → ∃ j' ∈ Rg, j < j' := by
    intro j hj hne
    have h1 := h.rread j hj
    rw [if_neg hne] at h1
    by_contra hcon
    push Not at hcon
    have h0 : readsIn C Rg (m + j) = 0 := by
      unfold readsIn
      apply Finset.sum_eq_zero
      intro j' hj'
      rw [List.count_eq_zero]
      intro hmem
      have h2 := h.rb j' (h.lt j' hj') (m + j) hmem
      have h3 := hcon j' hj'
      omega
    omega
  intro j hj
  by_contra hlt
  have hne : Rg.Nonempty := ⟨tj, h.tj_mem⟩
  have hM := Finset.max'_mem Rg hne
  have hMne : Rg.max' hne ≠ tj := by
    have h4 := Finset.le_max' Rg j hj
    omega
  obtain ⟨j', hj', hlt'⟩ := key _ hM hMne
  have h5 := Finset.le_max' Rg j' hj'
  omega

theorem no_out (C : Circuit) (Rg : Finset ℕ) (u : ℕ) (hsub : ∀ j ∈ Rg, j < C.size)
    (heq : readsIn C (Finset.range C.size) u = readsIn C Rg u) (j : ℕ) (hj : j < C.size)
    (hjR : j ∉ Rg) : u ∉ (gateAt C j).inputs := by
  unfold readsIn at heq
  have hs : Rg ⊆ Finset.range C.size := fun j hj => Finset.mem_range.mpr (hsub j hj)
  have h1 := Finset.sum_sdiff hs (f := fun j => (gateAt C j).inputs.count u)
  have hz : ∑ x ∈ Finset.range C.size \ Rg, (gateAt C x).inputs.count u = 0 := by omega
  have h2 := (Finset.sum_eq_zero_iff.mp hz) j (by simp [hj, hjR])
  exact List.count_eq_zero.mp h2

theorem wires_low (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  rw [wires_eq]; exact fold_stab _ _ _ hi

theorem blind (h : Reg m C S Rg tj bw) (x y : Fin m → Bool)
    (hxy : ∀ i : Fin m, (i : ℕ) ∉ S → x i = y i) :
    ∀ w, w < m + tj → w ∉ S → ¬ (m ≤ w ∧ w - m ∈ Rg) →
      (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hS hR
    by_cases hwm : w < m
    · rw [wires_low C _ w (by simpa using hwm), wires_low C _ w (by simpa using hwm)]
      have e : ∀ z : Fin m → Bool, (List.ofFn z).getD w false = z ⟨w, hwm⟩ := by
        intro z
        simp [List.getD_eq_getElem?_getD, hwm]
      rw [e x, e y]
      exact hxy ⟨w, hwm⟩ hS
    · obtain ⟨j, rfl⟩ : ∃ j, w = m + j := ⟨w - m, by omega⟩
      have hjR : j ∉ Rg := by
        intro hj
        exact hR ⟨by omega, by rw [show m + j - m = j by omega]; exact hj⟩
      have hjt : j < tj := by omega
      have hjs : j < C.size := lt_trans hjt (h.lt tj h.tj_mem)
      have vx := wire_val C.gates (List.ofFn x) j hjs
        (by intro i hi; rw [List.length_ofFn]; exact h.rb j hjs i hi)
      have vy := wire_val C.gates (List.ofFn y) j hjs
        (by intro i hi; rw [List.length_ofFn]; exact h.rb j hjs i hi)
      rw [List.length_ofFn] at vx vy
      rw [wires_eq, wires_eq, vx, vy]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi' : i < m + j := h.rb j hjs i hi
      refine ih i (by omega) (by omega) ?_ ?_
      · intro hiS
        exact no_out C Rg i h.lt (by rw [(h.sread i hiS).1, (h.sread i hiS).2]) j hjs hjR hi
      · rintro ⟨hmi, hiR⟩
        have hne : i - m ≠ tj := by omega
        have e : m + (i - m) = i := by omega
        have h6 := no_out C Rg (m + (i - m)) h.lt
          (by rw [h.rtot _ hiR hne, h.rread _ hiR, if_neg hne]) j hjs hjR
        rw [e] at h6
        exact h6 hi

theorem gc_one (h : Reg m C S Rg tj bw) : ∀ d, ∀ j ∈ Rg, C.size - j ≤ d →
    (form m C Rg (m + tj + 1) (m + tj)).gc j = 1 := by
  intro d
  induction d with
  | zero => intro j hj hd; have := h.lt j hj; omega
  | succ d ih =>
    intro j hj hd
    have e : m + j - m = j := by omega
    have hR : m ≤ m + j ∧ m + j - m ∈ Rg := ⟨by omega, by rw [e]; exact hj⟩
    have id := form_ident h (m + tj + 1) (m + tj) (by omega) (m + j)
    rw [if_pos hR, e, form_noR h _ _ (by omega) (m + j) hR] at id
    have hs : ∑ q ∈ Rg, (form m C Rg (m + tj + 1) (m + tj)).gc q *
        (gateAt C q).inputs.count (m + j) = readsIn C Rg (m + j) := by
      unfold readsIn
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hc : (gateAt C q).inputs.count (m + j) = 0
      · rw [hc, Nat.mul_zero]
      · have hmem : m + j ∈ (gateAt C q).inputs := by
          by_contra hn
          exact hc (List.count_eq_zero.mpr hn)
        have h2 := h.rb q (h.lt q hq) (m + j) hmem
        have h3 := h.lt q hq
        rw [ih q hq (by omega), Nat.one_mul]
    rw [hs, h.rread j hj] at id
    by_cases hjt : j = tj
    · have k1 : (if m + tj = m + j then 1 else 0) = 1 := if_pos (by omega)
      rw [k1, if_pos hjt] at id
      omega
    · have k1 : (if m + tj = m + j then 1 else 0) = 0 := if_neg (by omega)
      rw [k1, if_neg hjt] at id
      omega

theorem lc_eq (h : Reg m C S Rg tj bw) : ∀ u,
    (form m C Rg (m + tj + 1) (m + tj)).lc u =
      (if u ∈ S then 1 else 0) + (if u = bw then readsIn C Rg bw else 0) := by
  intro u
  have id := form_ident h (m + tj + 1) (m + tj) (by omega) u
  have hs : ∑ q ∈ Rg, (form m C Rg (m + tj + 1) (m + tj)).gc q *
      (gateAt C q).inputs.count u = readsIn C Rg u := by
    unfold readsIn
    apply Finset.sum_congr rfl
    intro q hq
    rw [gc_one h _ q hq le_rfl, Nat.one_mul]
  rw [hs] at id
  by_cases hc : m ≤ u ∧ u - m ∈ Rg
  · have hS : u ∉ S := fun hu => by have := h.Slt u hu; omega
    have hb : u ≠ bw := by rintro rfl; exact h.bwR hc
    rw [form_noR h _ _ (by omega) u hc, if_neg hS, if_neg hb]
  · rw [if_neg hc] at id
    have k1 : (if m + tj = u then 1 else 0) = 0 :=
      if_neg (by
        rintro rfl
        exact hc ⟨by omega, by rw [show m + tj - m = tj by omega]; exact h.tj_mem⟩)
    rw [k1] at id
    by_cases hS : u ∈ S
    · have hb : u ≠ bw := by rintro rfl; exact h.bwS hS
      rw [if_pos hS, if_neg hb]
      have h7 := (h.sread u hS).2
      omega
    · rw [if_neg hS]
      by_cases hb : u = bw
      · rw [if_pos hb]
        subst hb
        omega
      · rw [if_neg hb]
        have h8 : readsIn C Rg u = 0 := by
          unfold readsIn
          apply Finset.sum_eq_zero
          intro q hq
          rw [List.count_eq_zero]
          intro hmem
          rcases (h.gate q hq).2 u hmem with h1 | h1 | h1
          · exact hS h1
          · exact hc h1
          · exact hb h1
        omega

theorem sz_pos (S : Finset ℕ) (hc : 2 ≤ S.card) (t : T)
    (hl : ∀ u, t.lc u = if u ∈ S then 1 else 0) : 0 < t.sz := by
  cases t with
  | leaf i =>
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have h1 := hl a
    have h2 := hl b
    simp only [T.lc] at h1 h2
    rw [if_pos ha] at h1
    rw [if_pos hb] at h2
    have e1 : i = a := by
      by_contra hn
      rw [if_neg hn] at h1
      omega
    have e2 : i = b := by
      by_contra hn
      rw [if_neg hn] at h2
      omega
    omega
  | node j a l r => simp only [T.sz]; omega

theorem main (h : Reg m C S Rg tj bw) :
    ∃ (F : Circuit) (b : (Fin m → Bool) → Bool),
      (∀ g ∈ F.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      ReadsBack m F ∧ 0 < F.size ∧ F.output + 1 = m + F.size ∧
      (∀ i < m, readsIn F (Finset.range F.size) i = if i ∈ S then 1 else 0) ∧
      (∀ j < F.size, readsIn F (Finset.range F.size) (m + j) =
        if j + 1 = F.size then 0 else 1) ∧
      (∀ x y : Fin m → Bool, (∀ i : Fin m, (i : ℕ) ∉ S → x i = y i) → b x = b y) ∧
      ∀ x : Fin m → Bool,
        (C.wires (List.ofFn x)).getD (m + tj) false = (b x || F.eval (List.ofFn x)) := by
  have K : ∃ (t' : T) (b : (Fin m → Bool) → Bool), (∀ u, t'.lc u = if u ∈ S then 1 else 0) ∧
      (∀ x y : Fin m → Bool, (∀ i : Fin m, (i : ℕ) ∉ S → x i = y i) → b x = b y) ∧
      ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + tj) false =
        (b x || t'.ev (fun i => (C.wires (List.ofFn x)).getD i false)) := by
    have hlc := lc_eq h
    have hev := fun x : Fin m → Bool =>
      form_ev h (List.ofFn x) (by simp) (m + tj + 1) (m + tj) (by omega)
    rcases (by have := h.bw1; omega : readsIn C Rg bw = 0 ∨ readsIn C Rg bw = 1) with r0 | r1
    · refine ⟨form m C Rg (m + tj + 1) (m + tj), fun _ => false, ?_, fun _ _ _ => rfl, ?_⟩
      · intro u
        rw [hlc u, r0]
        simp
      · intro x
        rw [hev x]
        simp
    · have hb1 : (form m C Rg (m + tj + 1) (m + tj)).lc bw = 1 := by
        rw [hlc bw, if_neg h.bwS, if_pos rfl, r1]
      rcases rem bw _ hb1 (form_or h _ _ (by omega)).2 with hleaf | ⟨t', ht1, ht2⟩
      · exfalso
        obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by have := h.card; omega)
        have h1 := hlc a
        rw [hleaf, if_pos ha] at h1
        simp only [T.lc] at h1
        have hne : bw ≠ a := by rintro rfl; exact h.bwS ha
        rw [if_neg hne] at h1
        omega
      · refine ⟨t', fun x => (C.wires (List.ofFn x)).getD bw false, ?_, ?_, ?_⟩
        · intro u
          rw [ht1 u]
          by_cases hu : u = bw
          · rw [if_pos hu, hu, if_neg h.bwS]
          · rw [if_neg hu, hlc u, if_neg hu]
            simp
        · intro x y hxy
          have hlt : bw < m + tj := by
            have hne : readsIn C Rg bw ≠ 0 := by omega
            unfold readsIn at hne
            obtain ⟨p, hp, hpc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
            have hmem : bw ∈ (gateAt C p).inputs := by
              by_contra hn
              exact hpc (List.count_eq_zero.mpr hn)
            have h2 := h.rb p (h.lt p hp) bw hmem
            have h3 := tj_max h p hp
            omega
          exact blind h x y hxy bw hlt h.bwS h.bwR
        · intro x
          rw [← hev x, ht2]
  obtain ⟨t', b, hl, hbl, hval⟩ := K
  have hsz := sz_pos S h.card t' hl
  have hbel : t'.bel m := below_of m t' (fun u hu => by
    have h1 := hl u
    by_cases huS : u ∈ S
    · exact h.Slt u huS
    · rw [if_neg huS] at h1
      omega)
  have hlen : (cg m t' 0).length = t'.sz := cg_len m t' 0
  have hco := co_node m t' 0 hsz
  refine ⟨⟨cg m t' 0, m + t'.sz - 1⟩, b, ?_, ?_, ?_, ?_, ?_, ?_, hbl, ?_⟩
  · exact cg_ops m t' 0
  · intro j hj i hi
    have h1 := RB_get m _ 0 (cg_RB m t' 0 hbel) j hj i hi
    omega
  · show 0 < (cg m t' 0).length
    omega
  · show m + t'.sz - 1 + 1 = m + (cg m t' 0).length
    omega
  · intro i hi
    rw [readsIn_eq]
    show cnt i (cg m t' 0) = _
    have h1 := cnt_low m t' i hi 0
    have k1 : (if co m t' 0 = i then 1 else 0) = 0 := if_neg (by omega)
    rw [k1] at h1
    rw [← hl i]
    omega
  · intro j hj
    have hj' : j < (cg m t' 0).length := hj
    rw [readsIn_eq]
    show cnt (m + j) (cg m t' 0) = if j + 1 = (cg m t' 0).length then 0 else 1
    rw [hlen]
    have h1 := cnt_high m t' j 0 hbel
    have k0 : (if 0 ≤ j ∧ j < 0 + t'.sz then 1 else 0) = 1 := if_pos ⟨by omega, by omega⟩
    rw [k0] at h1
    by_cases hc : j + 1 = t'.sz
    · have k1 : (if co m t' 0 = m + j then 1 else 0) = 1 := if_pos (by omega)
      rw [k1] at h1
      rw [if_pos hc]
      omega
    · have k1 : (if co m t' 0 = m + j then 1 else 0) = 0 := if_neg (by omega)
      rw [k1] at h1
      rw [if_neg hc]
      omega
  · intro x
    rw [hval x]
    congr 1
    have e : m + t'.sz - 1 = co m t' 0 := by omega
    show _ = ((cg m t' 0).foldl step (List.ofFn x)).getD (m + t'.sz - 1) false
    rw [e, cg_sem m t' 0 (List.ofFn x) (by simp) hbel]
    apply ev_congr t' m hbel
    intro i hi
    exact wires_low C (List.ofFn x) i (by simpa using hi)

end

end PEqualNP.Outside.L_meta_21437_aux

theorem PEqualNP.Outside.L_meta_21437 : (∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (S Rg : Finset ℕ) (tj bw : ℕ),
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C → tj ∈ Rg → (∀ j ∈ Rg, j < C.size) →
  (∀ i ∈ S, i < m) → 2 ≤ S.card →
  (∀ j ∈ Rg,
    (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2) ∧
    ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
      w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg) ∨ w = bw) →
  bw ∉ S → ¬ (m ≤ bw ∧ bw - m ∈ Rg) →
  PEqualNP.MetaComplexity.NestedCover.readsIn C Rg bw ≤ 1 →
  (∀ i ∈ S, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) i = 1 ∧
    PEqualNP.MetaComplexity.NestedCover.readsIn C Rg i = 1) →
  (∀ j ∈ Rg, PEqualNP.MetaComplexity.NestedCover.readsIn C Rg (m + j) = if j = tj then 0 else 1) →
  (∀ j ∈ Rg, j ≠ tj → PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 1) →
  (∀ j ∈ Rg,
    Relation.TransGen (fun a c => m ≤ c ∧ c - m ∈ Rg ∧
      a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (c - m)).inputs) bw (m + j) →
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  ∃ (F : PEqualNP.CircuitLowerBounds.Circuit) (b : (Fin m → Bool) → Bool),
    (∀ g ∈ F.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack m F ∧ 0 < F.size ∧ F.output + 1 = m + F.size ∧
    (∀ i < m, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) i = if i ∈ S then 1 else 0) ∧
    (∀ j < F.size, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) (m + j) =
      if j + 1 = F.size then 0 else 1) ∧
    (∀ x y : Fin m → Bool, (∀ i : Fin m, (i : ℕ) ∉ S → x i = y i) → b x = b y) ∧
    ∀ x : Fin m → Bool,
      (C.wires (List.ofFn x)).getD (m + tj) false = (b x || F.eval (List.ofFn x))) := by
  intro m C S Rg tj bw h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  exact PEqualNP.Outside.L_meta_21437_aux.main ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
