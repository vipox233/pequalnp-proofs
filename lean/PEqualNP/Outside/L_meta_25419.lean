import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25419

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

-- FRAGMENT orchain    DEPENDS: fold mono restrict
-- OR chains over a list of existing wires placed at an offset b (the first chain gate is wire b), stars
-- x_c AND (OR of a list) and blocks of several stars, with their values, lengths, ReadsBack (RBo) and gate shapes.
-- Exports (w : List Bool is the wire list before the block, w.length = b):
--   def ocg t L b : OR chain: gates OR(t, L0) at wire b, OR(b, L1) at wire b + 1, ... (L.length gates)
--   def octop t L b : its top wire (t if L = [], else b + L.length - 1) ;  octop_nil, octop_cons (L ne []) ;  octop_lt (t < b) : octop t L b < b + L.length
--   ocg_len : (ocg t L b).length = L.length ;  ocg_gate : g in ocg t L b -> g.op = or and g.inputs.length = 2
--   ocg_val (w.length = b) (t < b) (all of L < b) :
--       (W (ocg t L b) w).getD (octop t L b) false = true iff (w.getD t false = true or exists i in L, w.getD i false = true)
--   ocg_rb (t < b) (all of L < b) : RBo b (ocg t L b)
--   def ostar c L b : the star x_c AND OR(L): [] if L = [], else ocg L0 (tail) b ++ [AND(c, top)] (L.length gates, star wire b + L.length - 1)
--   ostar_len : (ostar c L b).length = L.length ;  ostar_gate : g in ostar c L b -> (op and or or) and 2 inputs
--   ostar_val (L ne []) (w.length = b) (c < b) (all of L < b) :
--       (W (ostar c L b) w).getD (b + L.length - 1) false = true iff (w.getD c false = true and exists i in L, w.getD i false = true)
--   ostar_rb (c < b) (all of L < b) : RBo b (ostar c L b)
--   def ostars Lf cs b : stars of the centres cs (list of wires, block of centre c uses the list Lf c), one after the other
--   def ostarW Lf cs b d : the star wire of the first occurrence of centre d in cs
--   ostars_len : (ostars Lf cs b).length = (cs.map fun c => (Lf c).length).sum ;  ostars_gate : shapes as ostar_gate
--   ostars_val (w.length = b) (all c in cs, c < b) (all c in cs, all i in Lf c, i < b) (d in cs) (Lf d ne []) :
--       ostarW Lf cs b d < b + (ostars Lf cs b).length and ((W (ostars Lf cs b) w).getD (ostarW Lf cs b d) false = true
--       iff (w.getD d false = true and exists i in Lf d, w.getD i false = true))
--   ostars_rb (same bounds) : RBo b (ostars Lf cs b)
--   def ochain L b := chain OR over L at b (L.length - 1 gates, [] for L = [] or one wire) ;  def ochainTop L b : its top wire
--   ochain_len ;  ochain_gate (OR, 2 inputs) ;  ochain_rb (all of L < b) : RBo b (ochain L b)
--   ochain_val (L ne []) (w.length = b) (all of L < b) : ochainTop L b < b + (ochain L b).length and
--       ((W (ochain L b) w).getD (ochainTop L b) false = true iff exists i in L, w.getD i false = true)
--   def ochains Lf Xs b / ochainsW Lf Xs b d : one chain per key X (over the wire list Lf X), one after the other, and the top of key d
--   ochains_len : length = (Xs.map fun X => (Lf X).length - 1).sum ;  ochains_gate ;  ochains_rb (all wires < b)
--   ochains_val (w.length = b) (all wires < b) (d in Xs) (Lf d ne []) : ochainsW < b + length and
--       (value at ochainsW iff exists i in Lf d, w.getD i false = true)
--   oc_ex (all i in L, w1.getD i false = w.getD i false) : (exists i in L, w1 true) iff (exists i in L, w true)
-- Use: as the middle block of frag reorder (block placed after the kept head part, b = n + head part length); the star
-- wire values then come from ostars_val with w = the run of the head part, and frag reorder transports them.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def ocg : ℕ → List ℕ → ℕ → List Gate
  | _, [], _ => []
  | t, i :: L, b => ⟨GateOp.or, [t, i]⟩ :: ocg b L (b + 1)

def octop : ℕ → List ℕ → ℕ → ℕ
  | t, [], _ => t
  | _, _ :: L, b => octop b L (b + 1)

theorem oc_ex (L : List ℕ) (w1 w : List Bool) (h : ∀ i ∈ L, w1.getD i false = w.getD i false) :
    (∃ i ∈ L, w1.getD i false = true) ↔ (∃ i ∈ L, w.getD i false = true) := by
  constructor
  · rintro ⟨i, hi, h1⟩
    exact ⟨i, hi, by rw [← h i hi]; exact h1⟩
  · rintro ⟨i, hi, h1⟩
    exact ⟨i, hi, by rw [h i hi]; exact h1⟩

theorem ocg_len (L : List ℕ) : ∀ (t b : ℕ), (ocg t L b).length = L.length := by
  induction L with
  | nil => intro t b; rfl
  | cons i L ih =>
    intro t b
    show (ocg b L (b + 1)).length + 1 = L.length + 1
    rw [ih]

theorem octop_nil (t b : ℕ) : octop t [] b = t := rfl

theorem octop_cons (L : List ℕ) : ∀ (t b : ℕ), L ≠ [] → octop t L b = b + L.length - 1 := by
  induction L with
  | nil => intro t b h; exact absurd rfl h
  | cons i L ih =>
    intro t b _
    show octop b L (b + 1) = b + (L.length + 1) - 1
    by_cases h : L = []
    · subst h
      rfl
    · rw [ih b (b + 1) h]
      omega

theorem octop_lt (L : List ℕ) (t b : ℕ) (ht : t < b) : octop t L b < b + L.length := by
  by_cases h : L = []
  · subst h
    rw [octop_nil]
    simp
    exact ht
  · rw [octop_cons L t b h]
    have : L.length ≠ 0 := by
      intro h0
      exact h (List.length_eq_zero_iff.mp h0)
    omega

theorem ocg_gate (L : List ℕ) : ∀ (t b : ℕ) (g : Gate), g ∈ ocg t L b →
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction L with
  | nil => intro t b g hg; simp [ocg] at hg
  | cons i L ih =>
    intro t b g hg
    have hg' : g ∈ (⟨GateOp.or, [t, i]⟩ : Gate) :: ocg b L (b + 1) := hg
    rcases List.mem_cons.mp hg' with h1 | h1
    · subst h1
      exact ⟨rfl, rfl⟩
    · exact ih b (b + 1) g h1

theorem ocg_val (L : List ℕ) : ∀ (t b : ℕ) (w : List Bool), w.length = b → t < b → (∀ i ∈ L, i < b) →
    ((W (ocg t L b) w).getD (octop t L b) false = true ↔
      (w.getD t false = true ∨ ∃ i ∈ L, w.getD i false = true)) := by
  induction L with
  | nil =>
    intro t b w _ _ _
    simp [ocg, octop, W_nil]
  | cons i L ih =>
    intro t b w hw ht hL
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    have hs : ∀ a, a < b → (step w ⟨GateOp.or, [t, i]⟩).getD a false = w.getD a false :=
      fun a ha => step_lt w _ a (by omega)
    have hb : (step w ⟨GateOp.or, [t, i]⟩).getD b false = (w.getD t false || w.getD i false) := by
      rw [step_last w _ b hw.symm]
      simp [GateOp.eval]
    show (W (ocg b L (b + 1)) (step w ⟨GateOp.or, [t, i]⟩)).getD (octop b L (b + 1)) false = true ↔ _
    rw [ih b (b + 1) _ (by rw [step_len, hw]) (by omega) (fun a ha => by have := hL2 a ha; omega)]
    rw [hb, oc_ex L _ w (fun a ha => hs a (hL2 a ha))]
    constructor
    · rintro (h | ⟨a, ha, h⟩)
      · simp only [Bool.or_eq_true] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨i, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact Or.inr ⟨a, List.mem_cons.mpr (Or.inr ha), h⟩
    · rintro (h | ⟨a, ha, h⟩)
      · exact Or.inl (by rw [h]; rfl)
      · rcases List.mem_cons.mp ha with h2 | ha2
        · subst h2
          exact Or.inl (by rw [h, Bool.or_true])
        · exact Or.inr ⟨a, ha2, h⟩

theorem ocg_rb (L : List ℕ) : ∀ (t b : ℕ), t < b → (∀ i ∈ L, i < b) → RBo b (ocg t L b) := by
  induction L with
  | nil => intro t b _ _; exact RBo_nil b
  | cons i L ih =>
    intro t b ht hL
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    apply RBo_cons
    · intro a ha
      have ha' : a ∈ [t, i] := ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with h | h <;> omega
    · exact ih b (b + 1) (by omega)
        (fun a ha => by have := hL a (List.mem_cons.mpr (Or.inr ha)); omega)

def ostar : ℕ → List ℕ → ℕ → List Gate
  | _, [], _ => []
  | c, i :: L, b => ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩]

theorem ostar_len (c : ℕ) (L : List ℕ) (b : ℕ) : (ostar c L b).length = L.length := by
  cases L with
  | nil => rfl
  | cons i L =>
    show (ocg i L b ++ [_]).length = L.length + 1
    rw [List.length_append, ocg_len]
    rfl

theorem ostar_gate (c : ℕ) (L : List ℕ) (b : ℕ) (g : Gate) (hg : g ∈ ostar c L b) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  cases L with
  | nil => simp [ostar] at hg
  | cons i L =>
    have hg' : g ∈ ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩] := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · have := ocg_gate L i b g h1
      exact ⟨Or.inr this.1, this.2⟩
    · rw [List.mem_singleton] at h1
      subst h1
      exact ⟨Or.inl rfl, rfl⟩

theorem ostar_val (c : ℕ) (L : List ℕ) (b : ℕ) (w : List Bool) (hL0 : L ≠ []) (hw : w.length = b)
    (hc : c < b) (hL : ∀ i ∈ L, i < b) :
    ((W (ostar c L b) w).getD (b + L.length - 1) false = true ↔
      (w.getD c false = true ∧ ∃ i ∈ L, w.getD i false = true)) := by
  cases L with
  | nil => exact absurd rfl hL0
  | cons i L =>
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    show (W (ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩]) w).getD (b + (L.length + 1) - 1) false = true ↔ _
    have hlen : (W (ocg i L b) w).length = b + L.length := by rw [W_length, ocg_len, hw]
    rw [W_snoc, step_last _ _ _ (by rw [hlen]; omega)]
    have h1 : (W (ocg i L b) w).getD c false = w.getD c false := W_prefix _ w c (by omega)
    have h2 := ocg_val L i b w hw hi hL2
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, Bool.and_eq_true]
    rw [h1, h2]
    constructor
    · rintro ⟨hc1, h | ⟨a, ha, h⟩⟩
      · exact ⟨hc1, i, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact ⟨hc1, a, List.mem_cons.mpr (Or.inr ha), h⟩
    · rintro ⟨hc1, a, ha, h⟩
      refine ⟨hc1, ?_⟩
      rcases List.mem_cons.mp ha with h3 | h3
      · subst h3
        exact Or.inl h
      · exact Or.inr ⟨a, h3, h⟩

theorem ostar_rb (c : ℕ) (L : List ℕ) (b : ℕ) (hc : c < b) (hL : ∀ i ∈ L, i < b) :
    RBo b (ostar c L b) := by
  cases L with
  | nil => exact RBo_nil b
  | cons i L =>
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    show RBo b (ocg i L b ++ [⟨GateOp.and, [c, octop i L b]⟩])
    apply RBo_append _ _ _ (ocg_rb L i b hi hL2)
    apply RBo_cons _ _ _ _ (RBo_nil _)
    intro a ha
    have ha' : a ∈ [c, octop i L b] := ha
    have htop := octop_lt L i b hi
    rw [ocg_len]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    rcases ha' with h | h <;> omega

def ostars (Lf : ℕ → List ℕ) : List ℕ → ℕ → List Gate
  | [], _ => []
  | c :: cs, b => ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length)

def ostarW (Lf : ℕ → List ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | c :: cs, b, d => if c = d then b + (Lf c).length - 1 else ostarW Lf cs (b + (Lf c).length) d

theorem ostars_len (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ b,
    (ostars Lf cs b).length = (cs.map fun c => (Lf c).length).sum := by
  induction cs with
  | nil => intro b; rfl
  | cons c cs ih =>
    intro b
    show (ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length)).length = _
    rw [List.length_append, ostar_len, ih, List.map_cons, List.sum_cons]

theorem ostars_gate (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ b (g : Gate), g ∈ ostars Lf cs b →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  induction cs with
  | nil => intro b g hg; simp [ostars] at hg
  | cons c cs ih =>
    intro b g hg
    have hg' : g ∈ ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length) := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · exact ostar_gate c (Lf c) b g h1
    · exact ih _ g h1

theorem ostars_rb (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ b, (∀ c ∈ cs, c < b) →
    (∀ c ∈ cs, ∀ i ∈ Lf c, i < b) → RBo b (ostars Lf cs b) := by
  induction cs with
  | nil => intro b _ _; exact RBo_nil b
  | cons c cs ih =>
    intro b hc hi
    show RBo b (ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length))
    apply RBo_append _ _ _ (ostar_rb c (Lf c) b (hc c (List.mem_cons.mpr (Or.inl rfl)))
      (hi c (List.mem_cons.mpr (Or.inl rfl))))
    rw [ostar_len]
    apply ih
    · intro d hd
      have := hc d (List.mem_cons.mpr (Or.inr hd))
      omega
    · intro d hd i hi2
      have := hi d (List.mem_cons.mpr (Or.inr hd)) i hi2
      omega

theorem ostars_val (Lf : ℕ → List ℕ) (cs : List ℕ) : ∀ (b : ℕ) (w : List Bool), w.length = b →
    (∀ c ∈ cs, c < b) → (∀ c ∈ cs, ∀ i ∈ Lf c, i < b) → ∀ d ∈ cs, Lf d ≠ [] →
    ostarW Lf cs b d < b + (ostars Lf cs b).length ∧
    ((W (ostars Lf cs b) w).getD (ostarW Lf cs b d) false = true ↔
      (w.getD d false = true ∧ ∃ i ∈ Lf d, w.getD i false = true)) := by
  induction cs with
  | nil => intro b w _ _ _ d hd; simp at hd
  | cons c cs ih =>
    intro b w hw hc hi d hd hLd
    have hc0 : c < b := hc c (List.mem_cons.mpr (Or.inl rfl))
    have hi0 : ∀ i ∈ Lf c, i < b := hi c (List.mem_cons.mpr (Or.inl rfl))
    have hlen1 : (W (ostar c (Lf c) b) w).length = b + (Lf c).length := by
      rw [W_length, ostar_len, hw]
    have hpre : ∀ a, a < b → (W (ostar c (Lf c) b) w).getD a false = w.getD a false :=
      fun a ha => W_prefix _ w a (by omega)
    have eW : W (ostars Lf (c :: cs) b) w = W (ostars Lf cs (b + (Lf c).length)) (W (ostar c (Lf c) b) w) :=
      W_append _ _ w
    have eL : (ostars Lf (c :: cs) b).length = (Lf c).length + (ostars Lf cs (b + (Lf c).length)).length := by
      show (ostar c (Lf c) b ++ ostars Lf cs (b + (Lf c).length)).length = _
      rw [List.length_append, ostar_len]
    rw [eW, eL]
    by_cases hcd : c = d
    · subst hcd
      have ew : ostarW Lf (c :: cs) b c = b + (Lf c).length - 1 := by
        show (if c = c then b + (Lf c).length - 1 else _) = _
        rw [if_pos rfl]
      have hpos : (Lf c).length ≠ 0 := by
        intro h0
        exact hLd (List.length_eq_zero_iff.mp h0)
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [W_prefix _ _ _ (by omega)]
      exact ostar_val c (Lf c) b w hLd hw hc0 hi0
    · have ew : ostarW Lf (c :: cs) b d = ostarW Lf cs (b + (Lf c).length) d := by
        show (if c = d then b + (Lf c).length - 1 else _) = _
        rw [if_neg hcd]
      have hd2 : d ∈ cs := by
        rcases List.mem_cons.mp hd with h | h
        · exact absurd h.symm hcd
        · exact h
      have hcs : ∀ e ∈ cs, e < b := fun e he => hc e (List.mem_cons.mpr (Or.inr he))
      have his : ∀ e ∈ cs, ∀ i ∈ Lf e, i < b := fun e he => hi e (List.mem_cons.mpr (Or.inr he))
      obtain ⟨h1, h2⟩ := ih (b + (Lf c).length) _ hlen1
        (fun e he => by have := hcs e he; omega)
        (fun e he i hi2 => by have := his e he i hi2; omega) d hd2 hLd
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [h2, hpre d (hcs d hd2), oc_ex (Lf d) _ w (fun i hi2 => hpre i (his d hd2 i hi2))]

def ochain : List ℕ → ℕ → List Gate
  | [], _ => []
  | i :: L, b => ocg i L b

def ochainTop : List ℕ → ℕ → ℕ
  | [], _ => 0
  | i :: L, b => octop i L b

theorem ochain_len (L : List ℕ) (b : ℕ) : (ochain L b).length = L.length - 1 := by
  cases L with
  | nil => rfl
  | cons i L =>
    show (ocg i L b).length = L.length + 1 - 1
    rw [ocg_len]
    omega

theorem ochain_gate (L : List ℕ) (b : ℕ) (g : Gate) (hg : g ∈ ochain L b) :
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  cases L with
  | nil => simp [ochain] at hg
  | cons i L => exact ocg_gate L i b g hg

theorem ochain_rb (L : List ℕ) (b : ℕ) (hL : ∀ i ∈ L, i < b) : RBo b (ochain L b) := by
  cases L with
  | nil => exact RBo_nil b
  | cons i L =>
    exact ocg_rb L i b (hL i (List.mem_cons.mpr (Or.inl rfl)))
      (fun a ha => hL a (List.mem_cons.mpr (Or.inr ha)))

theorem ochain_val (L : List ℕ) (b : ℕ) (w : List Bool) (hL0 : L ≠ []) (hw : w.length = b)
    (hL : ∀ i ∈ L, i < b) :
    ochainTop L b < b + (ochain L b).length ∧
    ((W (ochain L b) w).getD (ochainTop L b) false = true ↔ ∃ i ∈ L, w.getD i false = true) := by
  cases L with
  | nil => exact absurd rfl hL0
  | cons i L =>
    have hi : i < b := hL i (List.mem_cons.mpr (Or.inl rfl))
    have hL2 : ∀ a ∈ L, a < b := fun a ha => hL a (List.mem_cons.mpr (Or.inr ha))
    refine ⟨?_, ?_⟩
    · show octop i L b < b + (ocg i L b).length
      rw [ocg_len]
      exact octop_lt L i b hi
    · show (W (ocg i L b) w).getD (octop i L b) false = true ↔ _
      rw [ocg_val L i b w hw hi hL2]
      constructor
      · rintro (h | ⟨a, ha, h⟩)
        · exact ⟨i, List.mem_cons.mpr (Or.inl rfl), h⟩
        · exact ⟨a, List.mem_cons.mpr (Or.inr ha), h⟩
      · rintro ⟨a, ha, h⟩
        rcases List.mem_cons.mp ha with h2 | h2
        · subst h2
          exact Or.inl h
        · exact Or.inr ⟨a, h2, h⟩

def ochains (Lf : ℕ → List ℕ) : List ℕ → ℕ → List Gate
  | [], _ => []
  | X :: Xs, b => ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length)

def ochainsW (Lf : ℕ → List ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | X :: Xs, b, d => if X = d then ochainTop (Lf X) b else ochainsW Lf Xs (b + (ochain (Lf X) b).length) d

theorem ochains_len (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ b,
    (ochains Lf Xs b).length = (Xs.map fun X => (Lf X).length - 1).sum := by
  induction Xs with
  | nil => intro b; rfl
  | cons X Xs ih =>
    intro b
    show (ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length)).length = _
    rw [List.length_append, ochain_len, ih, List.map_cons, List.sum_cons]

theorem ochains_gate (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ b (g : Gate), g ∈ ochains Lf Xs b →
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction Xs with
  | nil => intro b g hg; simp [ochains] at hg
  | cons X Xs ih =>
    intro b g hg
    have hg' : g ∈ ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length) := hg
    rcases List.mem_append.mp hg' with h1 | h1
    · exact ochain_gate (Lf X) b g h1
    · exact ih _ g h1

theorem ochains_rb (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ b, (∀ X ∈ Xs, ∀ i ∈ Lf X, i < b) →
    RBo b (ochains Lf Xs b) := by
  induction Xs with
  | nil => intro b _; exact RBo_nil b
  | cons X Xs ih =>
    intro b hi
    show RBo b (ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length))
    apply RBo_append _ _ _ (ochain_rb (Lf X) b (hi X (List.mem_cons.mpr (Or.inl rfl))))
    apply ih
    intro d hd i hi2
    have := hi d (List.mem_cons.mpr (Or.inr hd)) i hi2
    omega

theorem ochains_val (Lf : ℕ → List ℕ) (Xs : List ℕ) : ∀ (b : ℕ) (w : List Bool), w.length = b →
    (∀ X ∈ Xs, ∀ i ∈ Lf X, i < b) → ∀ d ∈ Xs, Lf d ≠ [] →
    ochainsW Lf Xs b d < b + (ochains Lf Xs b).length ∧
    ((W (ochains Lf Xs b) w).getD (ochainsW Lf Xs b d) false = true ↔
      ∃ i ∈ Lf d, w.getD i false = true) := by
  induction Xs with
  | nil => intro b w _ _ d hd; simp at hd
  | cons X Xs ih =>
    intro b w hw hi d hd hLd
    have hi0 : ∀ i ∈ Lf X, i < b := hi X (List.mem_cons.mpr (Or.inl rfl))
    have hlen1 : (W (ochain (Lf X) b) w).length = b + (ochain (Lf X) b).length := by
      rw [W_length, hw]
    have hpre : ∀ a, a < b → (W (ochain (Lf X) b) w).getD a false = w.getD a false :=
      fun a ha => W_prefix _ w a (by omega)
    have eW : W (ochains Lf (X :: Xs) b) w =
        W (ochains Lf Xs (b + (ochain (Lf X) b).length)) (W (ochain (Lf X) b) w) := W_append _ _ w
    have eL : (ochains Lf (X :: Xs) b).length =
        (ochain (Lf X) b).length + (ochains Lf Xs (b + (ochain (Lf X) b).length)).length := by
      show (ochain (Lf X) b ++ ochains Lf Xs (b + (ochain (Lf X) b).length)).length = _
      rw [List.length_append]
    rw [eW, eL]
    by_cases hXd : X = d
    · subst hXd
      have ew : ochainsW Lf (X :: Xs) b X = ochainTop (Lf X) b := by
        show (if X = X then ochainTop (Lf X) b else _) = _
        rw [if_pos rfl]
      obtain ⟨hlt, hv⟩ := ochain_val (Lf X) b w hLd hw hi0
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [W_prefix _ _ _ (by omega)]
      exact hv
    · have ew : ochainsW Lf (X :: Xs) b d = ochainsW Lf Xs (b + (ochain (Lf X) b).length) d := by
        show (if X = d then ochainTop (Lf X) b else _) = _
        rw [if_neg hXd]
      have hd2 : d ∈ Xs := by
        rcases List.mem_cons.mp hd with h | h
        · exact absurd h.symm hXd
        · exact h
      have his : ∀ e ∈ Xs, ∀ i ∈ Lf e, i < b := fun e he => hi e (List.mem_cons.mpr (Or.inr he))
      obtain ⟨h1, h2⟩ := ih (b + (ochain (Lf X) b).length) _ hlen1
        (fun e he i hi2 => by have := his e he i hi2; omega) d hd2 hLd
      rw [ew]
      refine ⟨by omega, ?_⟩
      rw [h2, oc_ex (Lf d) _ w (fun i hi2 => hpre i (his d hd2 i hi2))]

def pt (n a b : ℕ) : Fin (n + n) → Bool := fun k => decide (k.val = a) || decide (k.val = b)

theorem oneEach_pt (n : ℕ) (u v : Fin n) :
    PEqualNP.Represents.oneEach u v = List.ofFn (pt n u.val (n + v.val)) := by
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

theorem oe_len (n : ℕ) (u v : Fin n) : (PEqualNP.Represents.oneEach u v).length = n + n := by
  rw [oneEach_pt, List.length_ofFn]

theorem oe_getD (n : ℕ) (u v : Fin n) (k : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD k false = true ↔ (k = u.val ∨ k = n + v.val) := by
  rw [oneEach_pt]
  have hu := u.isLt
  have hv := v.isLt
  by_cases hk : k < n + n
  · rw [ofFn_getD _ k hk]
    simp [pt]
  · rw [ofFn_getD_ge _ k (by omega)]
    simp only [Bool.false_eq_true, false_iff]
    omega

def mS (n : ℕ) (S : Finset (Fin n)) (off : ℕ) : List ℕ :=
  ((List.finRange n).filter (fun a => decide (a ∈ S))).map (fun a => off + a.val)

def nS (n : ℕ) (S : Finset (Fin n)) (off : ℕ) : List ℕ :=
  ((List.finRange n).filter (fun a => !decide (a ∈ S))).map (fun a => off + a.val)

theorem mS_mem (n : ℕ) (S : Finset (Fin n)) (off i : ℕ) :
    i ∈ mS n S off ↔ ∃ a : Fin n, a ∈ S ∧ off + a.val = i := by
  simp [mS]

theorem nS_mem (n : ℕ) (S : Finset (Fin n)) (off i : ℕ) :
    i ∈ nS n S off ↔ ∃ a : Fin n, a ∉ S ∧ off + a.val = i := by
  simp [nS]

theorem mnS_len (n : ℕ) (S : Finset (Fin n)) (off : ℕ) :
    (mS n S off).length + (nS n S off).length = n := by
  simp only [mS, nS, List.length_map]
  rw [← List.length_eq_length_filter_add, List.length_finRange]

def Lf (n : ℕ) (S T : Finset (Fin n)) (d : ℕ) : List ℕ :=
  if d = 0 then mS n S 0 else if d = 1 then nS n S 0 else if d = 2 then mS n T n else nS n T n

theorem main_aux : ∀ (n : ℕ) (S T : Finset (Fin n)), 3 ≤ n → S.Nonempty → Sᶜ.Nonempty → T.Nonempty → Tᶜ.Nonempty → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) (2 * n - 1) := by
  intro n S T hn hS hSc hT hTc
  obtain ⟨s1, hs1⟩ := hS
  obtain ⟨s0, hs0⟩ := hSc
  obtain ⟨t1, ht1⟩ := hT
  obtain ⟨t0, ht0⟩ := hTc
  rw [Finset.mem_compl] at hs0 ht0
  have hL0 : Lf n S T 0 = mS n S 0 := by simp [Lf]
  have hL1 : Lf n S T 1 = nS n S 0 := by simp [Lf]
  have hL2 : Lf n S T 2 = mS n T n := by simp [Lf]
  have hL3 : Lf n S T 3 = nS n T n := by simp [Lf]
  have hne : ∀ d ∈ [0, 1, 2, 3], Lf n S T d ≠ [] := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · rw [hL0]; exact List.ne_nil_of_mem ((mS_mem _ _ _ _).2 ⟨s1, hs1, rfl⟩)
    · rw [hL1]; exact List.ne_nil_of_mem ((nS_mem _ _ _ _).2 ⟨s0, hs0, rfl⟩)
    · rw [hL2]; exact List.ne_nil_of_mem ((mS_mem _ _ _ _).2 ⟨t1, ht1, rfl⟩)
    · rw [hL3]; exact List.ne_nil_of_mem ((nS_mem _ _ _ _).2 ⟨t0, ht0, rfl⟩)
  have hbd : ∀ X ∈ [0, 1, 2, 3], ∀ i ∈ Lf n S T X, i < n + n := by
    intro X hX i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · rw [hL0, mS_mem] at hi; obtain ⟨a, _, rfl⟩ := hi; have := a.isLt; omega
    · rw [hL1, nS_mem] at hi; obtain ⟨a, _, rfl⟩ := hi; have := a.isLt; omega
    · rw [hL2, mS_mem] at hi; obtain ⟨a, _, rfl⟩ := hi; have := a.isLt; omega
    · rw [hL3, nS_mem] at hi; obtain ⟨a, _, rfl⟩ := hi; have := a.isLt; omega
  set O := ochains (Lf n S T) [0, 1, 2, 3] (n + n) with hO
  set L := O.length with hLdef
  set Wd := fun d => ochainsW (Lf n S T) [0, 1, 2, 3] (n + n) d with hWd
  have hLv : L + 4 = n + n := by
    rw [hLdef, hO, ochains_len]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hL0, hL1, hL2, hL3]
    have h1 := mnS_len n S 0
    have h2 := mnS_len n T n
    have e0 := List.length_pos_of_ne_nil (hne 0 (by simp))
    have e1 := List.length_pos_of_ne_nil (hne 1 (by simp))
    have e2 := List.length_pos_of_ne_nil (hne 2 (by simp))
    have e3 := List.length_pos_of_ne_nil (hne 3 (by simp))
    rw [hL0] at e0
    rw [hL1] at e1
    rw [hL2] at e2
    rw [hL3] at e3
    omega
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨⟨((O ++ [⟨GateOp.and, [Wd 0, Wd 2]⟩]) ++ [⟨GateOp.and, [Wd 1, Wd 3]⟩]) ++
      [⟨GateOp.or, [n + n + L, n + n + L + 1]⟩], n + n + L + 2⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with ((hg | rfl) | rfl) | rfl
    · have := ochains_gate _ _ _ g hg
      exact ⟨by rw [this.1]; simp, by rw [this.2]⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
  · show (((O ++ _) ++ _) ++ _).length ≤ 2 * n - 1
    simp only [List.length_append, List.length_singleton]
    omega
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    set w := PEqualNP.Represents.oneEach u v with hw
    have hwl : w.length = n + n := oe_len n u v
    have hval : ∀ d ∈ [0, 1, 2, 3], Wd d < n + n + L ∧
        ((W O w).getD (Wd d) false = true ↔ ∃ i ∈ Lf n S T d, w.getD i false = true) :=
      fun d hd => ochains_val _ _ (n + n) w hwl hbd d hd (hne d hd)
    have hsS : (∃ i ∈ mS n S 0, w.getD i false = true) ↔ u ∈ S := by
      constructor
      · rintro ⟨i, hi, hg⟩
        rw [mS_mem] at hi
        obtain ⟨a, ha, rfl⟩ := hi
        rw [hw, oe_getD] at hg
        have := a.isLt
        rcases hg with h | h
        · have e : a = u := Fin.ext (by omega)
          rwa [← e]
        · omega
      · intro h
        exact ⟨0 + u.val, (mS_mem _ _ _ _).2 ⟨u, h, rfl⟩, by rw [hw, oe_getD]; left; omega⟩
    have hsSc : (∃ i ∈ nS n S 0, w.getD i false = true) ↔ u ∉ S := by
      constructor
      · rintro ⟨i, hi, hg⟩
        rw [nS_mem] at hi
        obtain ⟨a, ha, rfl⟩ := hi
        rw [hw, oe_getD] at hg
        have := a.isLt
        rcases hg with h | h
        · have e : a = u := Fin.ext (by omega)
          rwa [← e]
        · omega
      · intro h
        exact ⟨0 + u.val, (nS_mem _ _ _ _).2 ⟨u, h, rfl⟩, by rw [hw, oe_getD]; left; omega⟩
    have hsT : (∃ i ∈ mS n T n, w.getD i false = true) ↔ v ∈ T := by
      constructor
      · rintro ⟨i, hi, hg⟩
        rw [mS_mem] at hi
        obtain ⟨a, ha, rfl⟩ := hi
        rw [hw, oe_getD] at hg
        have := a.isLt
        rcases hg with h | h
        · omega
        · have e : a = v := Fin.ext (by omega)
          rwa [← e]
      · intro h
        exact ⟨n + v.val, (mS_mem _ _ _ _).2 ⟨v, h, rfl⟩, by rw [hw, oe_getD]; right; rfl⟩
    have hsTc : (∃ i ∈ nS n T n, w.getD i false = true) ↔ v ∉ T := by
      constructor
      · rintro ⟨i, hi, hg⟩
        rw [nS_mem] at hi
        obtain ⟨a, ha, rfl⟩ := hi
        rw [hw, oe_getD] at hg
        have := a.isLt
        rcases hg with h | h
        · omega
        · have e : a = v := Fin.ext (by omega)
          rwa [← e]
      · intro h
        exact ⟨n + v.val, (nS_mem _ _ _ _).2 ⟨v, h, rfl⟩, by rw [hw, oe_getD]; right; rfl⟩
    obtain ⟨b0, v0⟩ := hval 0 (by simp)
    obtain ⟨b1, v1⟩ := hval 1 (by simp)
    obtain ⟨b2, v2⟩ := hval 2 (by simp)
    obtain ⟨b3, v3⟩ := hval 3 (by simp)
    rw [hL0, hsS] at v0
    rw [hL1, hsSc] at v1
    rw [hL2, hsT] at v2
    rw [hL3, hsTc] at v3
    have hOl : (W O w).length = n + n + L := by rw [W_length, hwl]
    have e1 : ∀ i, i < n + n + L →
        (W (O ++ [⟨GateOp.and, [Wd 0, Wd 2]⟩]) w).getD i false = (W O w).getD i false := by
      intro i hi
      rw [W_snoc_getD, if_neg (by rw [hwl]; omega)]
    have e2 : (W (O ++ [⟨GateOp.and, [Wd 0, Wd 2]⟩]) w).getD (n + n + L) false =
        ((W O w).getD (Wd 0) false && (W O w).getD (Wd 2) false) := by
      rw [W_snoc_getD, if_pos (by rw [hwl])]
      simp only [List.map_cons, List.map_nil, eval_and2]
    have e3 : ∀ i, i ≤ n + n + L →
        (W ((O ++ [⟨GateOp.and, [Wd 0, Wd 2]⟩]) ++ [⟨GateOp.and, [Wd 1, Wd 3]⟩]) w).getD i false =
        (W (O ++ [⟨GateOp.and, [Wd 0, Wd 2]⟩]) w).getD i false := by
      intro i hi
      rw [W_snoc_getD, if_neg (by simp only [List.length_append, List.length_singleton]; rw [hwl]; omega)]
    have e4 : (W ((O ++ [⟨GateOp.and, [Wd 0, Wd 2]⟩]) ++ [⟨GateOp.and, [Wd 1, Wd 3]⟩]) w).getD
        (n + n + L + 1) false = ((W O w).getD (Wd 1) false && (W O w).getD (Wd 3) false) := by
      rw [W_snoc_getD, if_pos (by simp only [List.length_append, List.length_singleton]; rw [hwl]; omega)]
      simp only [List.map_cons, List.map_nil, eval_and2]
      rw [e1 _ b1, e1 _ b3]
    show (W (((O ++ _) ++ _) ++ [⟨GateOp.or, [n + n + L, n + n + L + 1]⟩]) w).getD (n + n + L + 2) false = _
    rw [W_snoc_getD, if_pos (by simp only [List.length_append, List.length_singleton]; rw [hwl]; omega)]
    simp only [List.map_cons, List.map_nil, eval_or2]
    rw [e3 _ le_rfl, e2, e4]
    rw [Bool.eq_iff_iff, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, v0, v1, v2, v3]
    simp

end PEqualNP.Outside.L_meta_25419

theorem PEqualNP.Outside.L_meta_25419 : ∀ (n : ℕ) (S T : Finset (Fin n)), 3 ≤ n → S.Nonempty → Sᶜ.Nonempty → T.Nonempty → Tᶜ.Nonempty → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) (2 * n - 1) :=
  PEqualNP.Outside.L_meta_25419.main_aux
