import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25460

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

-- FRAGMENT restrict    DEPENDS: fold mono
-- Dropping a set S of gates that no kept gate reads (S read-closed), with renumbering of the kept wires
-- (rows 2774, 3312). Reading back with an offset (RBo) for gate lists built piece by piece.
-- Abbreviation: hcl = for all k < C.gates.length, k not in S -> for all i in (gateAt C k).inputs, i < n or i - n not in S.
-- Exports:
--   def RBo b gs : for all p < gs.length, every input i of gs.getD p (OR of nothing) has i < b + p
--       (RBo n C.gates is ReadsBack n C by unfolding; RBo n D.gates proves the ReadsBack part of IsAO2 n D)
--   RBo_nil b ;  RBo_cons (all inputs of g below b) (RBo (b + 1) gs) : RBo b (g :: gs)
--   RBo_append (RBo b g1) (RBo (b + g1.length) g2) : RBo b (g1 ++ g2)
--   def keepL S m := (List.range m).filter (not in S) ;  def rk S m := (keepL S m).length (new index of old gate m)
--   def rn n S w := if w < n then w else n + rk S (w - n)  (new wire of old wire w)
--   def mkG n C S j := gate j with inputs mapped by rn n S ;  def Dg n C S m := (keepL S m).map (mkG n C S)
--   keepL_succ_in / keepL_succ_out, Dg_succ_in (m in S) : Dg (m+1) = Dg m ;  Dg_succ_out : Dg (m+1) = Dg m ++ [mkG m]
--   rk_mono (a <= b) : rk S a <= rk S b ;  rk_lt (j < m) (j not in S) : rk S j < rk S m ;  rk_succ_out (m not in S) : rk S (m+1) = rk S m + 1
--   rn_lt (i < n + m) (i < n or i - n not in S) : rn n S i < n + rk S m ;  rn_gate : rn n S (n + o) = n + rk S o
--   Dg_len : (Dg n C S m).length = rk S m ;  keep_gate : j in keepL S C.gates.length -> gateAt C j in C.gates
--   restrict_val (ReadsBack n C) hcl (x.length = n) : for m <= len, (W (Dg n C S m) x).length = n + rk S m and
--       for every w < n + m with (w < n or w - n not in S), (W (Dg n C S m) x).getD (rn n S w) false = val C x w
--   restrict_rb (ReadsBack n C) hcl : m <= len -> RBo n (Dg n C S m)
--   restrict_size (all j in S below len) : (Dg n C S C.gates.length).length + S.card <= C.gates.length
--   restrict_circ (IsAO2 n C) hcl (S below len) (o < len, o not in S, C.output = n + o) :
--       exists D, IsAO2 n D and circuitFun n D = circuitFun n C and D.size + S.card <= C.size
--       (D = the circuit with gates Dg n C S C.gates.length and output n + rk S o)
-- Use: pick the dead set S, prove hcl, then restrict_circ; for other gate shapes use restrict_val / restrict_rb directly
-- (keep_gate transports per-gate properties such as op or fan-in). For S = gates outside the output cone see frag live.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def RBo (b : ℕ) (gs : List Gate) : Prop :=
  ∀ p < gs.length, ∀ i ∈ (gs.getD p ⟨GateOp.or, []⟩).inputs, i < b + p

theorem RBo_nil (b : ℕ) : RBo b [] := by
  intro p hp
  simp at hp

theorem RBo_cons (b : ℕ) (g : Gate) (gs : List Gate) (hg : ∀ i ∈ g.inputs, i < b)
    (h : RBo (b + 1) gs) : RBo b (g :: gs) := by
  intro p hp i hi
  cases p with
  | zero =>
    have hi' : i ∈ g.inputs := hi
    have := hg i hi'
    omega
  | succ q =>
    have hq : q < gs.length := by
      rw [List.length_cons] at hp
      omega
    have hi' : i ∈ (gs.getD q ⟨GateOp.or, []⟩).inputs := hi
    have := h q hq i hi'
    omega

theorem RBo_append (b : ℕ) (g1 g2 : List Gate) (h1 : RBo b g1)
    (h2 : RBo (b + g1.length) g2) : RBo b (g1 ++ g2) := by
  intro p hp i hi
  by_cases hlt : p < g1.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    exact h1 p hlt i hi
  · have hge : g1.length ≤ p := by omega
    rw [List.getD_append_right _ _ _ _ hge] at hi
    have hp2 : p - g1.length < g2.length := by
      rw [List.length_append] at hp
      omega
    have := h2 (p - g1.length) hp2 i hi
    omega

def keepL (S : Finset ℕ) (m : ℕ) : List ℕ := (List.range m).filter (fun j => !decide (j ∈ S))

def rk (S : Finset ℕ) (m : ℕ) : ℕ := (keepL S m).length

def rn (n : ℕ) (S : Finset ℕ) (w : ℕ) : ℕ := if w < n then w else n + rk S (w - n)

def mkG (n : ℕ) (C : Circuit) (S : Finset ℕ) (j : ℕ) : Gate :=
  ⟨(gateAt C j).op, (gateAt C j).inputs.map (rn n S)⟩

def Dg (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) : List Gate := (keepL S m).map (mkG n C S)

theorem keepL_succ_in (S : Finset ℕ) (m : ℕ) (h : m ∈ S) : keepL S (m + 1) = keepL S m := by
  simp [keepL, List.range_succ, List.filter_append, h]

theorem keepL_succ_out (S : Finset ℕ) (m : ℕ) (h : m ∉ S) :
    keepL S (m + 1) = keepL S m ++ [m] := by
  simp [keepL, List.range_succ, List.filter_append, h]

theorem rk_mono (S : Finset ℕ) (a b : ℕ) (h : a ≤ b) : rk S a ≤ rk S b := by
  unfold rk keepL
  exact ((List.range_sublist.mpr h).filter _).length_le

theorem rk_succ_out (S : Finset ℕ) (m : ℕ) (h : m ∉ S) : rk S (m + 1) = rk S m + 1 := by
  unfold rk
  rw [keepL_succ_out S m h, List.length_append, List.length_singleton]

theorem rk_lt (S : Finset ℕ) (j m : ℕ) (hj : j < m) (hS : j ∉ S) : rk S j < rk S m := by
  have h1 := rk_succ_out S j hS
  have h2 := rk_mono S (j + 1) m hj
  omega

theorem rn_lt (n : ℕ) (S : Finset ℕ) (i m : ℕ) (hi : i < n + m) (hS : i < n ∨ i - n ∉ S) :
    rn n S i < n + rk S m := by
  unfold rn
  by_cases h : i < n
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    have hS2 : i - n ∉ S := by
      rcases hS with h1 | h1
      · exact absurd h1 h
      · exact h1
    have := rk_lt S (i - n) m (by omega) hS2
    omega

theorem rn_gate (n : ℕ) (S : Finset ℕ) (o : ℕ) : rn n S (n + o) = n + rk S o := by
  unfold rn
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem Dg_succ_in (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) (h : m ∈ S) :
    Dg n C S (m + 1) = Dg n C S m := by
  unfold Dg
  rw [keepL_succ_in S m h]

theorem Dg_succ_out (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) (h : m ∉ S) :
    Dg n C S (m + 1) = Dg n C S m ++ [mkG n C S m] := by
  unfold Dg
  rw [keepL_succ_out S m h, List.map_append, List.map_singleton]

theorem Dg_len (n : ℕ) (C : Circuit) (S : Finset ℕ) (m : ℕ) : (Dg n C S m).length = rk S m := by
  unfold Dg rk
  rw [List.length_map]

theorem keep_gate (C : Circuit) (S : Finset ℕ) (j : ℕ) (hj : j ∈ keepL S C.gates.length) :
    gateAt C j ∈ C.gates := by
  have hjl : j < C.gates.length := by
    have := (List.mem_filter.mp hj).1
    exact List.mem_range.mp this
  exact gateAt_mem hjl

theorem restrict_val (n : ℕ) (C : Circuit) (S : Finset ℕ) (hRB : ReadsBack n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (x : List Bool) (hx : x.length = n) :
    ∀ m, m ≤ C.gates.length →
      (W (Dg n C S m) x).length = n + rk S m ∧
      ∀ w, w < n + m → (w < n ∨ w - n ∉ S) →
        (W (Dg n C S m) x).getD (rn n S w) false = val C x w := by
  have hsn : ∀ (l : List Bool) (b : Bool) (k : ℕ), l.length = k → (l ++ [b]).getD k false = b := by
    intro l b k hk
    subst hk
    exact getD_app_len l b
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · rw [W_length, Dg_len, hx]
    · intro w hw _
      have hw' : w < n := by omega
      have e : rn n S w = w := by unfold rn; rw [if_pos hw']
      rw [e, W_prefix (Dg n C S 0) x w (by omega), val_input hx hw']
  | succ m ih =>
    intro hm
    obtain ⟨hlen, hval⟩ := ih (by omega)
    by_cases hS : m ∈ S
    · have e2 : rk S (m + 1) = rk S m := by unfold rk; rw [keepL_succ_in S m hS]
      rw [Dg_succ_in n C S m hS, e2]
      refine ⟨hlen, ?_⟩
      intro w hw hk
      have hne : w ≠ n + m := by
        intro hwe
        rcases hk with h1 | h1
        · omega
        · apply h1
          have : w - n = m := by omega
          rw [this]
          exact hS
      exact hval w (by omega) hk
    · rw [Dg_succ_out n C S m hS, rk_succ_out S m hS, W_append]
      have hsingle : ∀ v : List Bool, W [mkG n C S m] v =
          v ++ [(gateAt C m).op.eval (((gateAt C m).inputs.map (rn n S)).map
            fun i => v.getD i false)] :=
        fun v => rfl
      rw [hsingle]
      refine ⟨?_, ?_⟩
      · rw [List.length_append, List.length_singleton, hlen]
        omega
      · intro w hw hk
        by_cases hwm : w = n + m
        · subst hwm
          rw [rn_gate, hsn _ _ _ hlen, val_gate_rb hx (by omega) (hRB m (by omega)), List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hval i (hRB m (by omega) i hi) (hcl m (by omega) hS i hi)
        · have hw2 : w < n + m := by omega
          rw [getD_app_lt _ _ _ (by rw [hlen]; exact rn_lt n S w m hw2 hk)]
          exact hval w hw2 hk

theorem restrict_rb (n : ℕ) (C : Circuit) (S : Finset ℕ) (hRB : ReadsBack n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S) :
    ∀ m, m ≤ C.gates.length → RBo n (Dg n C S m) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact RBo_nil n
  | succ m ih =>
    intro hm
    by_cases hS : m ∈ S
    · rw [Dg_succ_in n C S m hS]
      exact ih (by omega)
    · rw [Dg_succ_out n C S m hS]
      apply RBo_append _ _ _ (ih (by omega))
      apply RBo_cons _ _ _ _ (RBo_nil _)
      intro i hi
      have hi' : i ∈ (gateAt C m).inputs.map (rn n S) := hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi'
      rw [Dg_len]
      exact rn_lt n S i0 m (hRB m (by omega) i0 hi0) (hcl m (by omega) hS i0 hi0)

theorem restrict_size (n : ℕ) (C : Circuit) (S : Finset ℕ) (hS : ∀ j ∈ S, j < C.gates.length) :
    (Dg n C S C.gates.length).length + S.card ≤ C.gates.length := by
  have h3 : (List.range C.gates.length).length =
      ((List.range C.gates.length).filter (fun j => decide (j ∈ S))).length +
      ((List.range C.gates.length).filter (fun j => !decide (j ∈ S))).length :=
    List.length_eq_length_filter_add _
  have h4 : S.card ≤ ((List.range C.gates.length).filter (fun j => decide (j ∈ S))).length := by
    refine le_trans (Finset.card_le_card ?_)
      (List.toFinset_card_le (l := (List.range C.gates.length).filter (fun j => decide (j ∈ S))))
    intro j hj
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨List.mem_range.mpr (hS j hj), by simpa using hj⟩
  have h5 : (Dg n C S C.gates.length).length =
      ((List.range C.gates.length).filter (fun j => !decide (j ∈ S))).length := Dg_len n C S _
  rw [List.length_range] at h3
  omega

theorem restrict_circ (n : ℕ) (C : Circuit) (S : Finset ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hcl : ∀ k < C.gates.length, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (hS : ∀ j ∈ S, j < C.gates.length)
    (o : ℕ) (ho : o < C.gates.length) (hoS : o ∉ S) (hout : C.output = n + o) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + S.card ≤ C.size := by
  obtain ⟨hao, hRB, h2⟩ := hAO
  refine ⟨⟨Dg n C S C.gates.length, n + rk S o⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ (keepL S C.gates.length).map (mkG n C S) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    exact hao (gateAt C j) (keep_gate C S j hj)
  · exact restrict_rb n C S hRB hcl _ le_rfl
  · intro g hg
    have hg' : g ∈ (keepL S C.gates.length).map (mkG n C S) := hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
    have := h2 _ (keep_gate C S j hj)
    show ((gateAt C j).inputs.map (rn n S)).length = 2
    rw [List.length_map]
    exact this
  · funext x
    have h := (restrict_val n C S hRB hcl (List.ofFn x) (by simp) C.gates.length le_rfl).2 (n + o)
      (by omega) (Or.inr (by rw [Nat.add_sub_cancel_left]; exact hoS))
    rw [rn_gate] at h
    show (W (Dg n C S C.gates.length) (List.ofFn x)).getD (n + rk S o) false =
      val C (List.ofFn x) C.output
    rw [hout]
    exact h
  · exact restrict_size n C S hS

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

theorem getD_snoc_ne (L : List Bool) (a : Bool) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [a]).getD j false = L.getD j false := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact getD_snoc_lt L a j h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  unfold wf
  rw [List.foldl_append]

theorem wf_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g t ih =>
    intro w i hi
    rw [wf_cons, ih _ i (by simp; omega), getD_snoc_lt _ _ _ hi]

theorem blk_val (G : ℕ → Gate) (V : ℕ → Bool) (w : List Bool) : ∀ r : ℕ,
    (∀ i, i < w.length → w.getD i false = V i) →
    (∀ j, j < r → (∀ i ∈ (G j).inputs, i < w.length + j) ∧
      (G j).op.eval ((G j).inputs.map V) = V (w.length + j)) →
    ∀ i, i < w.length + r → (wf ((List.range r).map G) w).getD i false = V i := by
  intro r
  induction r with
  | zero =>
    intro hw _ i hi
    rw [List.range_zero, List.map_nil]
    exact hw i (by omega)
  | succ r ih =>
    intro hw hG i hi
    have ih' := ih hw (fun j hj => hG j (by omega))
    rw [List.range_succ, List.map_append, List.map_singleton, wf_append]
    have hlenA : (wf ((List.range r).map G) w).length = w.length + r := by rw [wf_len]; simp
    show (wf ((List.range r).map G) w ++ [(G r).op.eval ((G r).inputs.map fun i =>
      (wf ((List.range r).map G) w).getD i false)]).getD i false = V i
    by_cases hir : i < w.length + r
    · rw [getD_snoc_lt _ _ _ (by omega)]
      exact ih' i hir
    · obtain ⟨hin, hv⟩ := hG r (by omega)
      rw [show i = (wf ((List.range r).map G) w).length by omega, getD_snoc_eq, hlenA, ← hv]
      congr 1
      exact List.map_congr_left (fun i hi => ih' i (hin i hi))

theorem dd {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q := by
  simp only [h]

theorem dd2 {p q r : Prop} [Decidable p] [Decidable q] [Decidable r] (h : (p ∨ q) ↔ r) :
    (decide p || decide q) = decide r := by
  rw [← Bool.decide_or]
  exact dd h

def pre (o b t : ℕ) : ℕ := if t = 0 then o else b + (t - 1)

def suf (o k b t : ℕ) : ℕ := if t = 0 then o + (k - 1) else b + (k - 2 + t - 1)

def sg (o k b j : ℕ) : Gate :=
  if j < k - 2 then ⟨GateOp.or, [pre o b j, o + (j + 1)]⟩
  else if j < 2 * (k - 2) then ⟨GateOp.or, [o + (k - 2 - (j - (k - 2))), suf o k b (j - (k - 2))]⟩
  else ⟨GateOp.or, [pre o b (j - 2 * (k - 2)), suf o k b (k - 2 - 1 - (j - 2 * (k - 2)))]⟩

def blk (o k b : ℕ) : List Gate := (List.range (3 * (k - 2))).map (sg o k b)

def nus (o k b i : ℕ) : ℕ :=
  if i = 0 then suf o k b (k - 2) else if i = k - 1 then pre o b (k - 2) else b + (2 * (k - 2) + (i - 1))

def SEj (k u j : ℕ) : Bool :=
  if j < k - 2 then decide (u ≤ j + 1)
  else if j < 2 * (k - 2) then decide (k - 2 - (j - (k - 2)) ≤ u)
  else decide (u ≠ j - 2 * (k - 2) + 1)

theorem blk_len (o k b : ℕ) : (blk o k b).length = 3 * (k - 2) := by simp [blk]

theorem blk_ok (o k b : ℕ) : ∀ g ∈ blk o k b, g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [blk, List.mem_map, List.mem_range] at hg
  obtain ⟨j, _, rfl⟩ := hg
  unfold sg
  split_ifs <;> simp

theorem nus_lt (o k b i : ℕ) (hk : 2 ≤ k) (hi : i < k) (hob : o + k ≤ b) : nus o k b i < b + 3 * (k - 2) := by
  unfold nus pre suf
  split_ifs <;> omega

theorem side_ok (o k b u : ℕ) (w : List Bool) (hb : w.length = b) (hu : u < k) (hk : 2 ≤ k) (hob : o + k ≤ b)
    (hx : ∀ i, i < k → w.getD (o + i) false = decide (i = u)) :
    ∀ i, i < k → (wf (blk o k b) w).getD (nus o k b i) false = !decide (i = u) := by
  let V : ℕ → Bool := fun x => if x < b then w.getD x false else SEj k u (x - b)
  have hVi : ∀ i, i < k → V (o + i) = decide (i = u) := by
    intro i hi
    simp only [V, if_pos (show o + i < b by omega)]
    exact hx i hi
  have hVg : ∀ j, V (b + j) = SEj k u j := by
    intro j
    simp only [V, if_neg (show ¬ (b + j < b) by omega), Nat.add_sub_cancel_left]
  have hVp : ∀ t, t ≤ k - 2 → V (pre o b t) = decide (u ≤ t) := by
    intro t ht
    unfold pre
    split_ifs with h
    · have := hVi 0 (by omega)
      rw [Nat.add_zero] at this
      rw [this]
      exact dd (by omega)
    · rw [hVg]
      unfold SEj
      split_ifs <;> exact dd (by omega)
  have hVs : ∀ t, t ≤ k - 2 → V (suf o k b t) = decide (k - 1 - t ≤ u) := by
    intro t ht
    unfold suf
    split_ifs with h
    · rw [hVi (k - 1) (by omega)]
      exact dd (by omega)
    · rw [hVg]
      unfold SEj
      split_ifs <;> exact dd (by omega)
  have hv := blk_val (sg o k b) V w (3 * (k - 2))
    (fun i hi => by simp only [V, if_pos (show i < b by omega)])
    (by
      intro j hj
      rw [hb]
      unfold sg
      split_ifs with h1 h2
      · constructor
        · intro i hi
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
          rcases hi with rfl | rfl
          · unfold pre
            split_ifs <;> omega
          · omega
        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
            Bool.or_false, id_eq]
          rw [hVp j (by omega), hVi (j + 1) (by omega), hVg j]
          unfold SEj
          rw [if_pos h1]
          exact dd2 (by omega)
      · constructor
        · intro i hi
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
          rcases hi with rfl | rfl
          · omega
          · unfold suf
            split_ifs <;> omega
        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
            Bool.or_false, id_eq]
          rw [hVi (k - 2 - (j - (k - 2))) (by omega), hVs (j - (k - 2)) (by omega), hVg j]
          unfold SEj
          rw [if_neg h1, if_pos h2]
          exact dd2 (by omega)
      · constructor
        · intro i hi
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
          rcases hi with rfl | rfl
          · unfold pre
            split_ifs <;> omega
          · unfold suf
            split_ifs <;> omega
        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
            Bool.or_false, id_eq]
          rw [hVp (j - 2 * (k - 2)) (by omega), hVs (k - 2 - 1 - (j - 2 * (k - 2))) (by omega), hVg j]
          unfold SEj
          rw [if_neg h1, if_neg h2]
          exact dd2 (by omega))
  intro i hi
  show (wf ((List.range (3 * (k - 2))).map (sg o k b)) w).getD (nus o k b i) false = !decide (i = u)
  rw [hv _ (by rw [hb]; exact nus_lt o k b i hk hi hob), ← decide_not]
  unfold nus
  split_ifs with h1 h2
  · rw [hVs (k - 2) le_rfl]
    exact dd (by omega)
  · rw [hVp (k - 2) le_rfl]
    exact dd (by omega)
  · rw [hVg]
    unfold SEj
    split_ifs <;> exact dd (by omega)

open PEqualNP.MetaComplexity PEqualNP.Represents

theorem oe_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oe_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (h : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [h])]
  have e := getD_ofFn (fun j : Fin n => decide (j = u)) ⟨i, h⟩
  simp only at e
  rw [e]
  exact dd Fin.ext_iff

theorem oe_right {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (h : i < m) :
    (oneEach u v).getD (n + i) false = decide (i = v.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  have e := getD_ofFn (fun j : Fin m => decide (j = v)) ⟨i, h⟩
  simp only at e
  rw [e]
  exact dd Fin.ext_iff

def nuR (r c i : ℕ) : ℕ := if i < r then nus 0 r (r + c) i else nus r c (r + c + 3 * (r - 2)) (i - r)

def BBr (r c : ℕ) : ℕ := r + c + 3 * (r - 2) + 3 * (c - 2)

def mu (r c i : ℕ) : ℕ := if i < r + c then nuR r c i else BBr r c + (i - (r + c))

def dop (op : GateOp) : GateOp :=
  match op with
  | GateOp.and => GateOp.or
  | GateOp.or => GateOp.and
  | o => o

def dg (r c : ℕ) (g : Gate) : Gate := ⟨dop g.op, g.inputs.map (mu r c)⟩

def DG (r c : ℕ) (C : Circuit) : List Gate := C.gates.map (dg r c) ++ [⟨GateOp.and, []⟩]

theorem DG_len (r c : ℕ) (C : Circuit) : (DG r c C).length = C.gates.length + 1 := by
  simp [DG]

theorem DG_lt (r c : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (h : j < (DG r c C).length) :
    (DG r c C)[j] = dg r c (gateAt C j) := by
  have h1 : (DG r c C)[j]? = some (dg r c (gateAt C j)) := by
    unfold DG
    rw [List.getElem?_append_left (by simp; omega)]
    simp [hj, gateAt_eq hj]
  rw [List.getElem?_eq_getElem h] at h1
  exact Option.some.inj h1

theorem DG_last (r c : ℕ) (C : Circuit) (h : C.gates.length < (DG r c C).length) :
    (DG r c C)[C.gates.length] = ⟨GateOp.and, []⟩ := by
  have h1 : (DG r c C)[C.gates.length]? = some ⟨GateOp.and, []⟩ := by
    unfold DG
    rw [List.getElem?_append_right (by simp)]
    simp
  rw [List.getElem?_eq_getElem h] at h1
  exact Option.some.inj h1

def Dgs (r c : ℕ) (C : Circuit) : List Gate :=
  ((blk 0 r (r + c) ++ blk r c (r + c + 3 * (r - 2))) ++ C.gates.map (dg r c)) ++ [⟨GateOp.and, []⟩]

theorem dual_and (l : List Bool) : GateOp.or.eval (l.map (fun b => !b)) = !(GateOp.and.eval l) := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a <;> simp_all [GateOp.eval]

theorem dual_or (l : List Bool) : GateOp.and.eval (l.map (fun b => !b)) = !(GateOp.or.eval l) := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a <;> simp_all [GateOp.eval]

theorem sg_rb (o k b p : ℕ) (hk : 2 ≤ k) (hob : o + k ≤ b) (hp : p < 3 * (k - 2)) :
    ∀ i ∈ (sg o k b p).inputs, i < b + p := by
  intro i hi
  unfold sg pre suf at hi
  split_ifs at hi <;> simp at hi <;> omega

theorem blk_rbo (o k b : ℕ) (hk : 2 ≤ k) (hob : o + k ≤ b) : RBo b (blk o k b) := by
  intro p hp i hi
  rw [blk_len] at hp
  have e : (blk o k b).getD p ⟨GateOp.or, []⟩ = sg o k b p := by
    unfold blk
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  rw [e] at hi
  exact sg_rb o k b p hk hob hp i hi

theorem main_aux : ∀ (r c s : ℕ) (G : Fin r → Fin c → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ r → 2 ≤ c → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (r + c) C → C.size ≤ s → PEqualNP.Represents.Represents G C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r + c) D ∧ D.size ≤ s + (3 * r - 6) + (3 * c - 6) + 1 ∧ PEqualNP.Represents.Represents (fun u v => !(G u v)) D := by
  intro r c s G C hr hc hC hrb hs hrep
  set N := r + c with hN
  have hBB : BBr r c = N + 3 * (r - 2) + 3 * (c - 2) := rfl
  have hmuN : ∀ i, i < N → mu r c i < BBr r c := by
    intro i hi
    unfold mu nuR
    rw [if_pos hi]
    split_ifs with h
    · have := nus_lt 0 r (r + c) i hr h (by omega)
      rw [hBB]
      omega
    · have := nus_lt r c (r + c + 3 * (r - 2)) (i - r) hc (by omega) (by omega)
      rw [hBB]
      omega
  have hmuG : ∀ i, N ≤ i → mu r c i = BBr r c + (i - N) := by
    intro i hi
    unfold mu
    rw [if_neg (by omega)]
  have hlenB : (blk 0 r (r + c) ++ blk r c (r + c + 3 * (r - 2))).length = 3 * (r - 2) + 3 * (c - 2) := by
    rw [List.length_append, blk_len, blk_len]
  refine ⟨⟨Dgs r c C, if C.output < N + C.gates.length then mu r c C.output else BBr r c + C.gates.length⟩,
    ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [Dgs, List.mem_append, List.mem_singleton] at hg
    rcases hg with ((hg | hg) | hg) | rfl
    · have := blk_ok _ _ _ g hg
      exact ⟨by rw [this.1]; simp, this.2⟩
    · have := blk_ok _ _ _ g hg
      exact ⟨by rw [this.1]; simp, this.2⟩
    · simp only [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have h0 := hC g0 hg0
      have hop : g0.op = GateOp.and ∨ g0.op = GateOp.or := by simpa using h0.1
      refine ⟨?_, by simp only [dg, List.length_map]; exact h0.2⟩
      rcases hop with h | h <;> simp [dg, dop, h]
    · exact ⟨by simp, by simp⟩
  · show RBo N (Dgs r c C)
    unfold Dgs
    apply RBo_append
    · apply RBo_append
      · apply RBo_append
        · exact blk_rbo 0 r N hr (by omega)
        · rw [blk_len]
          exact blk_rbo r c (r + c + 3 * (r - 2)) hc (by omega)
      · intro p hp i hi
        rw [List.length_map] at hp
        rw [hlenB]
        have e : (C.gates.map (dg r c)).getD p ⟨GateOp.or, []⟩ = dg r c (gateAt C p) := by
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, gateAt_eq hp]
        rw [e] at hi
        simp only [dg, List.mem_map] at hi
        obtain ⟨i0, hi0, rfl⟩ := hi
        have h0 := hrb p hp i0 hi0
        by_cases hi0N : i0 < N
        · have := hmuN i0 hi0N
          rw [hBB] at this
          omega
        · rw [hmuG i0 (by omega), hBB]
          omega
    · intro p hp i hi
      simp at hp
      subst hp
      simp at hi
  · show (Dgs r c C).length ≤ _
    unfold Dgs
    simp only [List.length_append, List.length_map, List.length_singleton]
    rw [blk_len, blk_len]
    have : C.gates.length ≤ s := hs
    omega
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    set x := PEqualNP.Represents.oneEach u v with hx
    have hxl : x.length = N := oe_len u v
    set U1 := W (blk 0 r (r + c)) x with hU1
    set U2 := W (blk r c (r + c + 3 * (r - 2))) U1 with hU2
    have hU1l : U1.length = N + 3 * (r - 2) := by rw [hU1, W_length, hxl, blk_len]
    have hU2l : U2.length = BBr r c := by rw [hU2, W_length, hU1l, blk_len, hBB]
    have hpre : ∀ j, j < N → U2.getD j false = x.getD j false := fun j hj => by
      rw [hU2, W_prefix _ _ _ (by rw [hU1l]; omega), hU1, W_prefix _ _ _ (by rw [hxl]; exact hj)]
    have hneg : ∀ i, i < N → U2.getD (mu r c i) false = !x.getD i false := by
      intro i hi
      unfold mu nuR
      rw [if_pos hi]
      by_cases hir : i < r
      · rw [if_pos hir, oe_left u v i hir]
        have hs1 := side_ok 0 r (r + c) u.val x hxl u.isLt hr (by omega)
          (fun j hj => by rw [Nat.zero_add]; exact oe_left u v j hj) i hir
        have hlt := nus_lt 0 r (r + c) i hr hir (by omega)
        rw [hU2, W_prefix _ _ _ (by rw [hU1l]; omega), hU1]
        exact hs1
      · have ho := oe_right u v (i - r) (by omega)
        rw [show r + (i - r) = i by omega] at ho
        rw [if_neg hir, ho]
        have hs1 := side_ok r c (r + c + 3 * (r - 2)) v.val U1 hU1l v.isLt hc (by omega)
          (fun j hj => by rw [hU1, W_prefix _ _ _ (by rw [hxl]; omega)]; exact oe_right u v j hj)
          (i - r) (by omega)
        rw [hU2]
        exact hs1
    have hWD : W (Dgs r c C) x = W (DG r c C) (W (blk r c (r + c + 3 * (r - 2))) (W (blk 0 r (r + c)) x)) := by
      unfold Dgs
      rw [List.append_assoc, W_append (blk 0 r (r + c) ++ blk r c (r + c + 3 * (r - 2))),
        W_append (blk 0 r (r + c))]
      rfl
    rw [← hU1, ← hU2] at hWD
    have hgsl := DG_len r c C
    have key : ∀ w, w < N + C.gates.length → (W (DG r c C) U2).getD (mu r c w) false = !(val C x w) := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw
        by_cases hwN : w < N
        · rw [W_prefix _ _ _ (by rw [hU2l]; exact hmuN w hwN), hneg w hwN, val_input hxl hwN]
        · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
          have hj : j < C.gates.length := by omega
          rw [hmuG _ (by omega), show N + j - N = j by omega, ← hU2l]
          rw [W_gate (DG r c C) U2 j (by rw [hgsl]; omega)]
          rw [DG_lt r c C j hj, val_gate_rb hxl hj (hrb j hj)]
          have hm : ((dg r c (gateAt C j)).inputs.map fun i =>
              if i < U2.length + j then (W (DG r c C) U2).getD i false else false) =
              ((gateAt C j).inputs.map (val C x)).map (fun b => !b) := by
            simp only [dg, List.map_map]
            apply List.map_congr_left
            intro i0 hi0
            simp only [Function.comp_apply]
            have h0 := hrb j hj i0 hi0
            have hlt : mu r c i0 < U2.length + j := by
              rw [hU2l]
              by_cases hi0N : i0 < N
              · have := hmuN i0 hi0N
                omega
              · rw [hmuG i0 (by omega)]
                omega
            rw [if_pos hlt, ih i0 (by omega) (by omega)]
          rw [hm]
          have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
            simpa using (hC _ (gateAt_mem hj)).1
          rcases hop with h | h
          · simp only [dg, h, dop]
            exact dual_and _
          · simp only [dg, h, dop]
            exact dual_or _
    show (W (Dgs r c C) x).getD (if C.output < N + C.gates.length then mu r c C.output
      else BBr r c + C.gates.length) false = !(G u v)
    rw [← hrep u v, hWD]
    show _ = !(val C x C.output)
    by_cases ho : C.output < N + C.gates.length
    · rw [if_pos ho]
      exact key C.output ho
    · rw [if_neg ho, val_ge hxl (by omega), ← hU2l]
      have e := W_gate (DG r c C) U2 C.gates.length (by rw [hgsl]; omega)
      rw [e]
      rw [DG_last r c C]
      rfl

end PEqualNP.Outside.L_meta_25460

theorem PEqualNP.Outside.L_meta_25460 : ∀ (r c s : ℕ) (G : Fin r → Fin c → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ r → 2 ≤ c → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (r + c) C → C.size ≤ s → PEqualNP.Represents.Represents G C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r + c) D ∧ D.size ≤ s + (3 * r - 6) + (3 * c - 6) + 1 ∧ PEqualNP.Represents.Represents (fun u v => !(G u v)) D :=
  PEqualNP.Outside.L_meta_25460.main_aux
