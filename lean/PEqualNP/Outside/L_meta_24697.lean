import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24697

-- FRAGMENT fold    DEPENDS: (none)
-- Wire list as a fold over the gate list. C.wires x = W C.gates x (rfl), C.eval x = (W C.gates x).getD C.output false.
-- Exports:
--   def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
--   def W (gs : List Gate) (w : List Bool) := gs.foldl step w
--   wires_W C x : C.wires x = W C.gates x
--   eval_W C x : C.eval x = (W C.gates x).getD C.output false
--   circuitFun_W n C x : circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false
--   W_nil, W_cons : W (g :: gs) w = W gs (step w g), W_single : W [g] w = step w g
--   W_append : W (a ++ b) w = W b (W a w),  W_snoc : W (gs ++ [g]) w = step (W gs w) g
--   W_split j : W gs w = W (gs.drop j) (W (gs.take j) w)
--   step_len : (step w g).length = w.length + 1,  W_length : (W gs w).length = w.length + gs.length
--   getD_app_lt (i < l.length) : (l ++ l2).getD i false = l.getD i false
--   getD_app_len : (l ++ [v]).getD l.length false = v
--   getD_ge (l.length <= i) : l.getD i false = false
--   step_lt (i < w.length) : (step w g).getD i false = w.getD i false
--   step_last (k = w.length) : (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false)
--   W_prefix (i < w.length) : (W gs w).getD i false = w.getD i false
--   W_ge (w.length + gs.length <= i) : (W gs w).getD i false = false
--   W_snoc_getD : (W (gs ++ [g]) w).getD t false = if t = w.length + gs.length then (eval of g on W gs w) else (W gs w).getD t false
--   W_gate (j < gs.length) : (W gs w).getD (w.length + j) false
--        = gs[j].op.eval (gs[j].inputs.map fun i => if i < w.length + j then (W gs w).getD i false else false)
--   W_gate_pre (gs = pre ++ g :: post) : (W gs w).getD (w.length + pre.length) false = g.op.eval (g.inputs.map fun i => (W pre w).getD i false)
--   ofFn_getD (u < n) : (List.ofFn x).getD u false = x u
--   ofFn_getD_ge (n <= u) : (List.ofFn x).getD u false = false
--   split_gates (j < gs.length) : exists pre post, gs = pre ++ gs[j] :: post and pre.length = j
--   split2 (gs[j]? = some g) : exists pre post, pre.length = j, gs = pre ++ g :: post, and for all g2, gs.set j g2 = pre ++ g2 :: post
--   step_congr : same gate value on P gives same step
--   gateAt_eq (j < C.gates.length) : gateAt C j = C.gates[j],  gateAt_mem : gateAt C j in C.gates
--   gateAt_ge (C.gates.length <= j) : gateAt C j = (OR of nothing)
--   getElem?_gateAt : C.gates[j]? = some g -> gateAt C j = g and j < C.gates.length
--   eval_and_iff : GateOp.and.eval (l.map f) = true iff all i in l, f i = true
--   eval_or_iff : GateOp.or.eval (l.map f) = true iff exists i in l, f i = true
--   eval_and2 / eval_or2 : GateOp.and.eval [a, b] = (a and b) / GateOp.or.eval [a, b] = (a or b);  eval_or1 / eval_and1 : one operand copies it
-- Use: rewrite C.wires/eval/circuitFun into W, split the gate list at the changed gate with split2,
-- then compare W post (step P g1) with W post (step P g2) (W_prefix for wires below, W_gate for gate wires).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl

-- FRAGMENT mono    DEPENDS: fold
-- Wire values val, gate-by-gate value equations, monotonicity of AND/OR circuits, Monotone2 / IsAO2 facts,
-- minimal true points.
-- Exports:
--   def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false     (val C x u = (W C.gates x).getD u false by rfl)
--   eval_eq_val : C.eval x = val C x C.output ;  circuitFun_val : circuitFun n C x = val C (List.ofFn x) C.output
--   val_input (hx : x.length = n) (hu : u < n) : val C x u = x.getD u false
--   val_ofFn (u : Fin n) : val C (List.ofFn x) u.val = x u ;  val_ofFn_lt (hu : u < n) : val C (List.ofFn x) u = x (u, hu)
--   val_ge (hx : x.length = n) (hu : n + C.gates.length <= u) : val C x u = false
--   val_gate (hx : x.length = n) (hj : j < C.gates.length) :
--       val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => if i < n + j then val C x i else false)
--   val_gate_rb : same, without the if, when every input i of gate j has i < n + j (ReadsBack)
--   val_or  (op = or)  : val C x (n + r) = true iff exists i in inputs, i < n + r and val C x i = true
--   val_and (op = and) : val C x (n + r) = true iff all i in inputs, i < n + r and val C x i = true
--   and_val (IsAO2, op = and) : val C x (n + j) = (val of input 0 && val of input 1)  (inputs.getD 0 0 / getD 1 0)
--   or_val  (IsAO2, op = or)  : val C x (n + j) = (val of input 0 || val of input 1)
--   def OpMono R : AND and OR are monotone for relation R on Bool ;  opMono_eq : OpMono Eq ;  opMono_imp : OpMono (a = true -> b = true)
--   andOrOnly_of_monotone2 : Monotone2 C -> AndOrOnly C ;  andOrOnly_of_isAO2 : IsAO2 n C -> AndOrOnly C
--   mono (AndOrOnly C) (x <= y pointwise) : for all w, val C (ofFn x) w = true -> val C (ofFn y) w = true
--   circuitFun_mono (AndOrOnly C) (x <= y) : circuitFun n C x = true -> circuitFun n C y = true
--   monotone2_len : Monotone2 C -> g in C.gates -> g.inputs.length <= 2 ;  isAO2_len : IsAO2 n C -> g in C.gates -> g.inputs.length = 2
--   isAO2_rb : IsAO2 n C -> j < C.gates.length -> i in (gateAt C j).inputs -> i < n + j
--   def tr y : Finset of true coordinates ;  tr_lt : z < y strictly -> (tr z).card < (tr y).card
--   exists_min F x (F x = true) : exists y <= x, F y = true and every z < y (z <= y, z ne y) has F z = false
-- Use: induction on the wire index w (Nat.strong_induction_on) with val_input / val_ge / val_gate to compare two runs.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

theorem opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

theorem opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

theorem val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

theorem val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

theorem andOrOnly_of_monotone2 {C : Circuit} (h : Monotone2 C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := by
  intro g hg
  have h1 := (h g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem andOrOnly_of_isAO2 {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := h.1

theorem monotone2_len {C : Circuit} (h : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length ≤ 2 := (h g hg).2

theorem isAO2_len {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length = 2 := h.2.2 g hg

theorem isAO2_rb {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) {i : ℕ} (hi : i ∈ (gateAt C j).inputs) : i < n + j :=
  h.2.1 j hj i hi

theorem mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

theorem circuitFun_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
    (h : circuitFun n C x = true) : circuitFun n C y = true :=
  mono n C hAO x y hxy C.output h

theorem and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) &&
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem or_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) ||
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

def tr {n : ℕ} (y : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => y i = true)

theorem tr_lt {n : ℕ} (z y : Fin n → Bool) (hzy : ∀ i, z i = true → y i = true) (hne : z ≠ y) :
    (tr z).card < (tr y).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hzy i hi
  · intro heq
    apply hne
    funext i
    have h : i ∈ tr z ↔ i ∈ tr y := by rw [heq]
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact Bool.eq_iff_iff.mpr h

theorem exists_min {n : ℕ} (F : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : F x = true) :
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ F y = true ∧
      ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y → F z = false := by
  let S : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun y => F y = true ∧ ∀ i, y i = true → x i = true)
  have hS : S.Nonempty := ⟨x, by simp [S, hx]⟩
  obtain ⟨y, hyS, hmin⟩ := Finset.exists_min_image S (fun y => (tr y).card) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hyS
  refine ⟨y, hyS.2, hyS.1, ?_⟩
  intro z hzy hne
  cases hz : F z
  · rfl
  · exfalso
    have hzS : z ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz, fun i hi => hyS.2 i (hzy i hi)⟩
    have h1 := hmin z hzS
    have h2 := tr_lt z y hzy hne
    omega

def pt (n m a b : ℕ) : Fin (n + m) → Bool := fun k => decide (k.val = a) || decide (k.val = b)

theorem oneEach_pt (n m : ℕ) (u : Fin n) (v : Fin m) :
    PEqualNP.Represents.oneEach u v = List.ofFn (pt n m u.val (n + v.val)) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  have hu := u.isLt
  have hv := v.isLt
  congr 1
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_castAdd, Fin.coe_castLE]
    omega
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.coe_natAdd]
    omega

theorem oe_getD (n m : ℕ) (u : Fin n) (v : Fin m) (k : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD k false = true ↔ (k = u.val ∨ k = n + v.val) := by
  rw [oneEach_pt]
  have hu := u.isLt
  have hv := v.isLt
  by_cases hk : k < n + m
  · rw [ofFn_getD _ k hk]
    simp [pt]
  · rw [ofFn_getD_ge _ k (by omega)]
    simp only [Bool.false_eq_true, false_iff]
    omega

theorem oe_len (n m : ℕ) (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  rw [oneEach_pt, List.length_ofFn]

def sg (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (w : ℕ) : ℕ :=
  if h : w < n then (π.symm ⟨w, h⟩).val
  else if h2 : w < n + m then n + (ρ.symm ⟨w - n, by omega⟩).val else w

def rg (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (sg n m π ρ)⟩

def Cr (n m : ℕ) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rg n m π ρ), sg n m π ρ C.output⟩

theorem sg_ge {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (w : ℕ) (hw : n + m ≤ w) :
    sg n m π ρ w = w := by
  unfold sg
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem sg_lt {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (w : ℕ) (hw : w < n + m) :
    sg n m π ρ w < n + m := by
  unfold sg
  split_ifs with h1 h2
  · exact Nat.lt_of_lt_of_le (Fin.isLt _) (by omega)
  · exact Nat.add_lt_add_left (Fin.isLt _) n

theorem key_in {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (u : Fin n) (v : Fin m)
    (w : ℕ) (hw : w < n + m) :
    (sg n m π ρ w = u.val ∨ sg n m π ρ w = n + v.val) ↔ (w = (π u).val ∨ w = n + (ρ v).val) := by
  have hu := u.isLt
  have hv := v.isLt
  have hpu := (π u).isLt
  have hrv := (ρ v).isLt
  unfold sg
  split_ifs with h1 h2
  · have hlt := Fin.isLt (π.symm ⟨w, h1⟩)
    constructor
    · rintro (h | h)
      · left
        have e : π.symm ⟨w, h1⟩ = u := Fin.ext h
        rw [Equiv.symm_apply_eq] at e
        exact congrArg Fin.val e
      · omega
    · rintro (h | h)
      · left
        have e : (⟨w, h1⟩ : Fin n) = π u := Fin.ext h
        rw [← Equiv.symm_apply_eq] at e
        exact congrArg Fin.val e
      · omega
  · have hlt := Fin.isLt (ρ.symm ⟨w - n, by omega⟩)
    constructor
    · rintro (h | h)
      · omega
      · right
        have e : ρ.symm ⟨w - n, by omega⟩ = v := Fin.ext (by omega)
        rw [Equiv.symm_apply_eq] at e
        have e2 := congrArg Fin.val e
        simp only at e2
        omega
    · rintro (h | h)
      · omega
      · right
        have e : (⟨w - n, by omega⟩ : Fin m) = ρ v := Fin.ext (by simp only; omega)
        rw [← Equiv.symm_apply_eq] at e
        have e2 := congrArg Fin.val e
        omega

theorem sg_row {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (u : Fin n) (w : ℕ)
    (h : sg n m π ρ w = u.val) : w = (π u).val := by
  have hu := u.isLt
  unfold sg at h
  split_ifs at h with h1 h2
  · have e : π.symm ⟨w, h1⟩ = u := Fin.ext h
    rw [Equiv.symm_apply_eq] at e
    exact congrArg Fin.val e
  · omega
  · omega

theorem sg_col {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (v : Fin m) (w : ℕ)
    (h : sg n m π ρ w = n + v.val) : w = n + (ρ v).val := by
  have hv := v.isLt
  unfold sg at h
  split_ifs at h with h1 h2
  · have := Fin.isLt (π.symm ⟨w, h1⟩)
    omega
  · have e : ρ.symm ⟨w - n, by omega⟩ = v := Fin.ext (by omega)
    rw [Equiv.symm_apply_eq] at e
    have e2 := congrArg Fin.val e
    simp only at e2
    omega
  · omega

theorem Cr_gateAt {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (C : Circuit) (j : ℕ) :
    gateAt (Cr n m π ρ C) j = rg n m π ρ (gateAt C j) := by
  unfold gateAt Cr
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases C.gates[j]? <;> rfl

theorem Cr_len {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (C : Circuit) :
    (Cr n m π ρ C).gates.length = C.gates.length := by
  simp [Cr]

theorem wires_eq {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (C : Circuit)
    (u : Fin n) (v : Fin m) : ∀ k,
    val (Cr n m π ρ C) (PEqualNP.Represents.oneEach u v) (sg n m π ρ k) =
      val C (PEqualNP.Represents.oneEach (π u) (ρ v)) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < n + m
    · rw [val_input (oe_len n m u v) (sg_lt π ρ k hk), val_input (oe_len n m (π u) (ρ v)) hk,
        Bool.eq_iff_iff, oe_getD, oe_getD]
      exact key_in π ρ u v k hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = n + m + j := ⟨k - (n + m), by omega⟩
      rw [sg_ge π ρ _ (by omega)]
      by_cases hj : j < C.gates.length
      · rw [val_gate (oe_len n m u v) (by rw [Cr_len]; exact hj),
          val_gate (oe_len n m (π u) (ρ v)) hj, Cr_gateAt]
        unfold rg
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro w hw
        simp only [Function.comp_apply]
        by_cases hw2 : w < n + m + j
        · have hs : sg n m π ρ w < n + m + j := by
            by_cases hwn : w < n + m
            · have := sg_lt π ρ w hwn
              omega
            · rw [sg_ge π ρ w (by omega)]
              exact hw2
          rw [if_pos hs, if_pos hw2, ih w hw2]
        · rw [sg_ge π ρ w (by omega), if_neg hw2, if_neg hw2]
      · rw [val_ge (oe_len n m u v) (by rw [Cr_len]; omega),
          val_ge (oe_len n m (π u) (ρ v)) (by omega)]

theorem count_map' (f : ℕ → ℕ) (a b : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, f x = b ↔ x = a) →
    (l.map f).count b = l.count a := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x l ih =>
    intro h
    have hx := h x (List.mem_cons_self ..)
    rw [List.map_cons, List.count_cons, List.count_cons, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    by_cases e : x = a
    · have e2 : f x = b := hx.2 e
      subst e
      simp [e2]
    · have e2 : f x ≠ b := fun h' => e (hx.1 h')
      simp [e, e2]

theorem main_aux : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.Represents.Represents A C → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, C2.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.FanInTwo C2) ∧ (PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.Monotone2 C2) ∧ (((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C ∧ 0 < C.size ∧ C.output + 1 = (n + m) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + m) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + m))) → ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m)))) ∧ PEqualNP.Represents.Represents (fun u v => A (π u) (ρ v)) C2 ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (π u).val ∈ g.inputs) ∨ C.output = (π u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (ρ v).val) ∈ g.inputs) ∨ C.output = (n + (ρ v).val))) := by
  intro n m A π ρ C hrep
  refine ⟨Cr n m π ρ C, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (Cr n m π ρ C).gates.length = C.gates.length
    exact Cr_len π ρ C
  · intro hF g hg
    simp only [Cr, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact ⟨(hF g0 hg0).1, by simp only [rg, List.length_map]; exact (hF g0 hg0).2⟩
  · intro hM g hg
    simp only [Cr, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact ⟨(hM g0 hg0).1, by simp only [rg, List.length_map]; exact (hM g0 hg0).2⟩
  · intro hR
    have hlen := Cr_len π ρ C
    have hsz : (Cr n m π ρ C).size = C.size := hlen
    rcases hR with ⟨hsh, hrb, hpos, hout, hreads⟩ | ⟨h0, hlt⟩
    · have hoN : n + m ≤ C.output := by
        have : C.size = C.gates.length := rfl
        omega
      left
      refine ⟨?_, ?_, by rw [hsz]; exact hpos, ?_, ?_⟩
      · intro g hg
        simp only [Cr, List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        simp only [rg, List.length_map]
        exact hsh g0 hg0
      · intro j hj i hi
        rw [Cr_len] at hj
        rw [Cr_gateAt] at hi
        simp only [rg, List.mem_map] at hi
        obtain ⟨i0, hi0, rfl⟩ := hi
        have h0 := hrb j hj i0 hi0
        by_cases hN : i0 < n + m
        · have := sg_lt π ρ i0 hN
          omega
        · rw [sg_ge π ρ i0 (by omega)]
          exact h0
      · show sg n m π ρ C.output + 1 = n + m + (Cr n m π ρ C).size
        rw [sg_ge π ρ _ hoN, hsz]
        exact hout
      · intro j hj
        rw [hsz] at hj ⊢
        rw [← hreads j hj]
        unfold PEqualNP.MetaComplexity.NestedCover.readsIn
        constructor <;> intro h <;> rw [← h] <;> apply Finset.sum_congr rfl <;> intro j' _ <;>
          rw [Cr_gateAt] <;> simp only [rg] <;>
          first
          | exact (count_map' _ _ _ _ (fun x _ => by
              constructor
              · intro e
                by_cases hx : x < n + m
                · have := sg_lt π ρ x hx
                  omega
                · rw [sg_ge π ρ x (by omega)] at e
                  exact e
              · intro e
                rw [e, sg_ge π ρ _ (by omega)])).symm
          | exact (count_map' _ _ _ _ (fun x _ => by
              constructor
              · intro e
                by_cases hx : x < n + m
                · have := sg_lt π ρ x hx
                  omega
                · rw [sg_ge π ρ x (by omega)] at e
                  exact e
              · intro e
                rw [e, sg_ge π ρ _ (by omega)]))
    · right
      exact ⟨by rw [hsz]; exact h0, sg_lt π ρ _ hlt⟩
  · intro u v
    show val (Cr n m π ρ C) (PEqualNP.Represents.oneEach u v) (sg n m π ρ C.output) = _
    rw [wires_eq]
    exact hrep (π u) (ρ v)
  · intro u h
    rcases h with ⟨g, hg, hu⟩ | ho
    · simp only [Cr, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      simp only [rg, List.mem_map] at hu
      obtain ⟨w, hw, hwe⟩ := hu
      exact Or.inl ⟨g0, hg0, by rw [← sg_row π ρ u w hwe]; exact hw⟩
    · exact Or.inr (sg_row π ρ u _ ho)
  · intro v h
    rcases h with ⟨g, hg, hv⟩ | ho
    · simp only [Cr, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      simp only [rg, List.mem_map] at hv
      obtain ⟨w, hw, hwe⟩ := hv
      exact Or.inl ⟨g0, hg0, by rw [← sg_col π ρ v w hwe]; exact hw⟩
    · exact Or.inr (sg_col π ρ v _ ho)

end PEqualNP.Outside.L_meta_24697

theorem PEqualNP.Outside.L_meta_24697 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.Represents.Represents A C → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, C2.size = C.size ∧ (PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.FanInTwo C2) ∧ (PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.Monotone2 C2) ∧ (((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C ∧ 0 < C.size ∧ C.output + 1 = (n + m) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + m) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + m))) → ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m)))) ∧ PEqualNP.Represents.Represents (fun u v => A (π u) (ρ v)) C2 ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (π u).val ∈ g.inputs) ∨ C.output = (π u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (ρ v).val) ∈ g.inputs) ∨ C.output = (n + (ρ v).val))) :=
  PEqualNP.Outside.L_meta_24697.main_aux
