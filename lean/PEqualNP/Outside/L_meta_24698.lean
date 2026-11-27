import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24698

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

-- FRAGMENT elimvar    DEPENDS: fold
-- Gate elimination of one variable: fixing input v := b in a FanInTwo circuit (AND, OR, NOT, fan-in <= 2) and
-- propagating constants (the Stat simplifier: each old wire becomes a constant Sum.inl c or a new wire Sum.inr j)
-- removes every gate that reads v, so the restricted function has a circuit with at least one gate less.
-- Exports:
--   elim_one_var (v : Fin m) (b) (HasCircuitSize m F s) (F depends on v somewhere) (F with v := b is not constant) :
--       1 <= s and HasCircuitSize m (fun x => F (Function.update x v b)) (s - 1)
--   ev_elim_last n C (FanInTwo C) (C.eval (ofFn x ++ [false]) not constant in x) (some x: C.eval (ofFn x ++ [true]) ne
--       C.eval (ofFn x ++ [false])) : exists D, FanInTwo D, D.size < C.size, D.eval (ofFn x ++ [false]) = C.eval (ofFn x ++ [false])
--   ev_W_cons : W (g :: gs) w = W gs (w ++ [value of g]) (rfl) ;  ev_getD_snoc_lt / _eq / _ne : getD on l ++ [x] (any type)
--   def ev_OkGate g : op in and/or/not and fan-in <= 2 (FanInTwo per gate) ;  ev_NOkGate : also NOT has fan-in <= 1
--   def ev_normGate (NOT keeps its first input) ;  ev_normGate_eval, ev_normGate_nok, ev_W_norm : W (gs.map ev_normGate) w = W gs w
--   def ev_statVal w (Sum.inl c => c, Sum.inr j => w.getD j false) ;  def ev_statValid m s : a Sum.inr j has j < m
--   def ev_simp op m ins : (optional new gate, stat of the result) for AND/OR/NOT over stats (ev_simpAnd/Or/Not)
--   ev_simp_ok : new gates are ev_OkGate ;  ev_simp_sound : value preserved ;  ev_simp_none_of_const : a constant read gives no gate
--   ev_simp_and_false / ev_simp_or_true / ev_simp_not_const : explicit constant cases
--   def ev_elimStep m acc g / ev_elimPass m gs acc : the pass (acc = stats of old wires, new gate list)
--   ev_elimPass_cons/_append/_nil/_fst_len/_getD_lt/_ok ;  ev_elimPass_len : new length <= old + gs.length
--   ev_elimPass_len_lt (const wire k read by a gate of gs) : new + 1 <= ;  ev_elimPass_len_two (read by >= 2 gates) : new + 2 <=
--   def ev_Inv m w_in w_old acc : the invariant (stats valid and evaluate to the old wires) ;  ev_Inv_step, ev_Inv_pass
--   def ev_initVar m v b : stats of the inputs with v := b ;  ev_Inv_initVar ;  ev_ofFn_getD_lt (any type)
--   ev_W_agree : two wire lists agreeing outside B stay so if no gate reads B
--   ev_ofFn_snoc_eq : ofFn (Fin.snoc x b) = ofFn x ++ [b] ;  ev_eval_update_snoc
-- Use: elim_one_var for HasCircuitSize rows (2535); ev_elim_last for rows on C.eval (ofFn x ++ [b]) (2315);
-- for a two-gate saving reuse the proof of elim_one_var with ev_elimPass_len_two.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem ev_W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem ev_getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

theorem ev_getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

theorem ev_getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact ev_getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def ev_OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def ev_NOkGate (g : Gate) : Prop :=
  ev_OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def ev_normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem ev_normGate_eval (g : Gate) (F : ℕ → Bool) :
    (ev_normGate g).op.eval ((ev_normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [ev_normGate]
  cases inputs <;> simp [GateOp.eval]

theorem ev_normGate_nok (g : Gate) (h : ev_OkGate g) : ev_NOkGate (ev_normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [ev_normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [ev_normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [ev_normGate]
    · simp [ev_normGate]

theorem ev_W_norm (gs : List Gate) (w : List Bool) :
    W (gs.map ev_normGate) w = W gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, ev_W_cons, ev_W_cons, ev_normGate_eval, ih]

def ev_statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def ev_statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def ev_simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def ev_simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def ev_simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def ev_simp (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => ev_simpAnd m ins
  | GateOp.or => ev_simpOr m ins
  | GateOp.not => ev_simpNot m ins
  | _ => (none, Sum.inl false)

theorem ev_simp_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (ev_simp op m ins).1, ev_OkGate g := by
  intro g hg
  cases op <;> simp only [ev_simp] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [ev_simpAnd] at hg
    subst hg; simp [ev_OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [ev_simpOr] at hg
    subst hg; simp [ev_OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [ev_simpNot] at hg
    subst hg; simp [ev_OkGate]
  · simp at hg
  · simp at hg

theorem ev_simp_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (ev_simp op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [ev_simp, ev_simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [ev_simp, ev_simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [ev_simp, ev_simpNot]

theorem ev_simp_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    ev_simp GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [ev_simp, ev_simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [ev_simp, ev_simpAnd]
      | inr j => cases c <;> simp_all [ev_simp, ev_simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [ev_simp, ev_simpAnd]
      | inr j => simp at hf
  · simp at hlen

theorem ev_simp_not_const (m : ℕ) (c : Bool) :
    ev_simp GateOp.not m [Sum.inl c] = (none, Sum.inl (!c)) := rfl

theorem ev_simp_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, ev_statValid w.length s) :
    ev_statValid (w.length + (ev_simp op w.length ins).1.toList.length)
      (ev_simp op w.length ins).2 ∧
    ev_statVal (W (ev_simp op w.length ins).1.toList w)
      (ev_simp op w.length ins).2 = op.eval (ins.map (ev_statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval]
    · cases a <;> simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval, W, step]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval, W, step]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval, W, step]
        | inr j => simp_all [ev_simp, ev_simpAnd, ev_statValid, ev_statVal, GateOp.eval, W, step]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval]
    · cases a <;> simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval, W, step]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval, W, step]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval, W, step]
        | inr j => simp_all [ev_simp, ev_simpOr, ev_statValid, ev_statVal, GateOp.eval, W, step]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [ev_simp, ev_simpNot, ev_statValid, ev_statVal, GateOp.eval]
    · cases a <;> simp_all [ev_simp, ev_simpNot, ev_statValid, ev_statVal, GateOp.eval, W, step]

def ev_elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := ev_simp g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def ev_elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (ev_elimStep m) acc

theorem ev_elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    ev_elimPass m (g :: gs) acc = ev_elimPass m gs (ev_elimStep m acc g) := rfl

theorem ev_elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    ev_elimPass m (gs₁ ++ gs₂) acc = ev_elimPass m gs₂ (ev_elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, ev_elimPass_cons, ih]

theorem ev_elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (ev_elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [ev_elimPass]
  | cons g gs ih =>
    rw [ev_elimPass_cons, ih]
    simp [ev_elimStep]
    omega

theorem ev_elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (ev_elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [ev_elimPass_cons, ih _ (by simp [ev_elimStep]; omega)]
    exact ev_getD_snoc_lt _ _ _ _ hk

theorem ev_toList_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem ev_elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, ev_OkGate g) : ∀ g ∈ (ev_elimPass m gs acc).2, ev_OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [ev_elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact ev_simp_ok _ _ _ g' (by simpa using h1)

theorem ev_elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (ev_elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [ev_elimPass]
  | cons g gs ih =>
    rw [ev_elimPass_cons, List.length_cons]
    have h1 := ih (ev_elimStep m acc g)
    have h2 : (ev_elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [ev_elimStep, List.length_append]
      have := ev_toList_len_le (ev_simp g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

theorem ev_elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, ev_NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (ev_elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [ev_elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (ev_simp g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply ev_simp_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (ev_elimStep m acc g).2.length = acc.2.length := by
        simp only [ev_elimStep, hnone, Option.toList_none, List.append_nil]
      have := ev_elimPass_len m gs (ev_elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (ev_elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [ev_elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [ev_elimStep]; rw [ev_getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (ev_elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [ev_elimStep, List.length_append]
        have := ev_toList_len_le (ev_simp g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem ev_elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, ev_NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (ev_elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [ev_elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (ev_simp g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply ev_simp_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (ev_elimStep m acc g).2.length = acc.2.length := by
        simp only [ev_elimStep, hnone, Option.toList_none, List.append_nil]
      have hfilt : 1 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simp [hkg] at htwo
        omega
      have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        have hne : gs.filter (fun g => decide (k ∈ g.inputs)) ≠ [] := by
          intro hnil; rw [hnil] at hfilt; simp at hfilt
        obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
        rw [List.mem_filter] at hg'
        exact ⟨g', hg'.1, of_decide_eq_true hg'.2⟩
      have h1 := ev_elimPass_len_lt m k gs (ev_elimStep m acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [ev_elimStep]; omega)
        ⟨c, by simp only [ev_elimStep]; rw [ev_getD_snoc_lt _ _ _ _ hk]; exact hc⟩
        hex'
      omega
    · have htwo' : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simpa [hkg] using htwo
      have h1 := ih (ev_elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [ev_elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [ev_elimStep]; rw [ev_getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        htwo'
      have h2 : (ev_elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [ev_elimStep, List.length_append]
        have := ev_toList_len_le (ev_simp g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

def ev_Inv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    ev_statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    ev_statVal (W acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

theorem ev_Inv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : ev_OkGate g)
    (hinv : ev_Inv m w_in w_old acc) :
    ev_Inv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (ev_elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := W acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, W_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, ev_statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := ev_simp_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [ev_elimStep, hlen], ?_⟩
  intro i
  simp only [ev_elimStep]
  by_cases hieq : i = acc.1.length
  · rw [ev_getD_snoc_eq _ _ _ _ hieq, ev_getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [W_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [ev_getD_snoc_ne _ _ _ _ hieq, ev_getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [ev_statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [ev_statValid] at hv
        simp only [ev_statVal] at hval ⊢
        rw [W_append, ← hw_new, W_prefix _ _ _ (by omega)]
        exact hval

theorem ev_Inv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, ev_OkGate g) (hinv : ev_Inv m w_in w_old acc) :
    ev_Inv m w_in (W gs w_old) (ev_elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [ev_W_cons, ev_elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (ev_Inv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

theorem ev_ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

def ev_initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

theorem ev_Inv_initVar (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ev_Inv m (List.ofFn x) (List.ofFn (Function.update x v b)) (ev_initVar m v b, []) := by
  refine ⟨by simp, by simp [ev_initVar], ?_⟩
  intro i
  by_cases hi : i < m
  · have hget : (ev_initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr i := by
      rw [ev_initVar, ev_ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, ev_statValid, ev_statVal]
      rw [ev_ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, ev_statValid, ev_statVal, W_nil]
      refine ⟨by omega, ?_⟩
      rw [ev_ofFn_getD_lt _ _ _ hi, ev_ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [ev_initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem ev_simp_or_true (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (ht : Sum.inl true ∈ ins) :
    ev_simp GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at ht
  · cases a <;> simp_all [ev_simp, ev_simpOr]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [ev_simp, ev_simpOr]
      | inr j => cases c <;> simp_all [ev_simp, ev_simpOr]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [ev_simp, ev_simpOr]
      | inr j => simp at ht
  · simp at hlen

theorem ev_elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    ev_elimPass m [] acc = acc := rfl

theorem ev_W_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (W gs w₁).length = (W gs w₂).length ∧
    ∀ i ∉ B, (W gs w₁).getD i false = (W gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [ev_W_cons, ev_W_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [ev_getD_snoc_lt _ _ _ _ hlt, ev_getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [ev_getD_snoc_eq _ _ _ _ heq, ev_getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

theorem elim_one_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m) (b : Bool)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b)) :
    1 ≤ s ∧ HasCircuitSize m (fun x => F (Function.update x v b)) (s - 1) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map ev_normGate with hgs
  have hnok : ∀ g ∈ gs, ev_NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ev_normGate_nok g0 (hok g0 hg0)
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw1 : (C.wires (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b := by
      show (W C.gates (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b
      rw [W_prefix _ _ _ (by simp), ev_ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b := by
      show (W C.gates (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b
      rw [W_prefix _ _ _ (by simp), ev_ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw1
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := ev_W_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp)
      (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi
        simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
            intro h; apply hi; exact congrArg Fin.val h
          rw [ev_ofFn_getD_lt _ _ _ hlt, ev_ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg i hi hmem
        simp at hmem
        subst hmem
        exact hno' g hg hi)
    have hco : C.output ∉ ({(v : ℕ)} : Set ℕ) := by simpa using hout_ne
    have hEq := hag.2 C.output hco
    rw [hgs, ev_W_norm, ev_W_norm] at hEq
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := ev_elimPass m gs (ev_initVar m v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ gs.length := by
    have := ev_elimPass_len_lt m (v : ℕ) gs (ev_initVar m v b, []) hnok
      (by simp [ev_initVar])
      ⟨b, by rw [ev_initVar, ev_ofFn_getD_lt _ _ _ v.isLt]; simp⟩
      hex
    rw [← hacc] at this
    simpa using this
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hval : ∀ x : Fin m → Bool,
      ev_statVal (W acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        F (Function.update x v b) := by
    intro x
    have hinv := ev_Inv_pass m (List.ofFn x) gs _ (ev_initVar m v b, [])
      (fun g hg => (hnok g hg).1) (ev_Inv_initVar m v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2, hgs, ev_W_norm]
    exact hev (Function.update x v b)
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨by omega, ⟨acc.2, j⟩, ev_elimPass_ok m gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s - 1
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this


theorem ev_ofFn_snoc_eq {n : ℕ} (x : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc (α := fun _ => Bool) x b) = List.ofFn x ++ [b] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

theorem ev_eval_update_snoc {n : ℕ} (C : Circuit) (x : Fin n → Bool) (b c : Bool) :
    C.eval (List.ofFn (Function.update (Fin.snoc (α := fun _ => Bool) x c) (Fin.last n) b)) =
      C.eval (List.ofFn x ++ [b]) := by
  rw [Fin.update_snoc_last, ev_ofFn_snoc_eq]

theorem ev_elim_last : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), x2.eval (List.ofFn x4 ++ [Bool.false]) ≠ x2.eval (List.ofFn x5 ++ [Bool.false])) → (∃ (x5 : Fin x1 → Bool), x2.eval (List.ofFn x5 ++ [Bool.true]) ≠ x2.eval (List.ofFn x5 ++ [Bool.false])) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size < x2.size ∧ ∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7 ++ [Bool.false]) = x2.eval (List.ofFn x7 ++ [Bool.false]) := by
  intro n C hfan hnc0 hdep0
  have hdep : ∃ y : Fin (n + 1) → Bool,
      (fun z : Fin (n + 1) → Bool => C.eval (List.ofFn z)) (Function.update y (Fin.last n) false) ≠
      (fun z : Fin (n + 1) → Bool => C.eval (List.ofFn z)) (Function.update y (Fin.last n) true) := by
    obtain ⟨x, hx⟩ := hdep0
    refine ⟨Fin.snoc (α := fun _ => Bool) x false, ?_⟩
    show C.eval (List.ofFn (Function.update (Fin.snoc (α := fun _ => Bool) x false) (Fin.last n) false)) ≠
      C.eval (List.ofFn (Function.update (Fin.snoc (α := fun _ => Bool) x false) (Fin.last n) true))
    rw [ev_eval_update_snoc, ev_eval_update_snoc]
    exact fun h => hx h.symm
  have hnc : ∃ y y' : Fin (n + 1) → Bool,
      (fun z : Fin (n + 1) → Bool => C.eval (List.ofFn z)) (Function.update y (Fin.last n) false) ≠
      (fun z : Fin (n + 1) → Bool => C.eval (List.ofFn z)) (Function.update y' (Fin.last n) false) := by
    obtain ⟨x, x', hx⟩ := hnc0
    refine ⟨Fin.snoc (α := fun _ => Bool) x false, Fin.snoc (α := fun _ => Bool) x' false, ?_⟩
    show C.eval (List.ofFn (Function.update (Fin.snoc (α := fun _ => Bool) x false) (Fin.last n) false)) ≠
      C.eval (List.ofFn (Function.update (Fin.snoc (α := fun _ => Bool) x' false) (Fin.last n) false))
    rw [ev_eval_update_snoc, ev_eval_update_snoc]
    exact hx
  obtain ⟨hs, D, hD, hDs, hDv⟩ := elim_one_var (m := n + 1) (s := C.size)
    (F := fun z : Fin (n + 1) → Bool => C.eval (List.ofFn z)) (Fin.last n) false
    ⟨C, hfan, le_refl _, fun _ => rfl⟩ hdep hnc
  refine ⟨D, hD, by omega, ?_⟩
  intro x
  have h := hDv (Fin.snoc (α := fun _ => Bool) x false)
  have h' : D.eval (List.ofFn (Fin.snoc (α := fun _ => Bool) x false)) =
      C.eval (List.ofFn (Function.update (Fin.snoc (α := fun _ => Bool) x false) (Fin.last n) false)) := h
  rw [ev_eval_update_snoc, ev_ofFn_snoc_eq] at h'
  exact h'

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

-- FRAGMENT cones    DEPENDS: fold mono
-- Strict cones (PEqualNP.EdgeOwnership.cones / coneStep / InCone), PEqualNP.Core.coneSet, the leaves of a cone,
-- and: the value of a gate depends only on the inputs read inside its cone.
-- Exports (EO = PEqualNP.EdgeOwnership):
--   cones_len gs cs : (gs.foldl (EO.coneStep n) cs).length = cs.length + gs.length ;  cones_length : (EO.cones n C).length = C.gates.length
--   cones_char gs : i in (gs.foldl (coneStep n) []).getD j [] iff j < gs.length and exists w in (gs.getD j (OR of nothing)).inputs,
--       n <= w, w < n + j, (i = w - n or i in (fold).getD (w - n) [])
--   inCone_iff : EO.InCone n C i j iff j < C.gates.length and exists k, k < j and n + k in (gateAt C j).inputs and (i = k or InCone n C i k)
--   inCone_lt : InCone n C i j -> i < j and j < C.gates.length
--   inCone_of_read (j < C.gates.length) (k < j) (n + k in (gateAt C j).inputs) : InCone n C k j
--   inCone_trans : InCone n C i k -> InCone n C k j -> InCone n C i j
--   inCone_irrefl : not InCone n C j j
--   mem_coneSet : i in PEqualNP.Core.coneSet n C j iff i = j or InCone n C i j
--   self_mem_coneSet : j in coneSet n C j ;  coneSet_mono : InCone n C k j -> coneSet n C k subset coneSet n C j
--   coneSet_le (i in coneSet n C j) : i <= j ;  coneSet_sub_range (j < C.gates.length) : coneSet n C j subset Finset.range C.gates.length
--   def coneLeaves n C j : Finset (Fin n) := the inputs t with t read by some gate of coneSet n C j
--   mem_coneLeaves : t in coneLeaves n C j iff exists i in coneSet n C j, t.val in (gateAt C i).inputs
--   coneLeaves_mono : InCone n C k j -> coneLeaves n C k subset coneLeaves n C j
--   cone_agree (x, x' agree on coneLeaves n C j) : val C (List.ofFn x) (n + j) = val C (List.ofFn x') (n + j)
--   cone_agree_gateVal : same for EO.gateVal n C j x = EO.gateVal n C j x'
--   def coneRd n C z w : n <= w, w < n + C.gates.length, z in (gateAt C (w - n)).inputs  (wire w reads wire z)
--   coneRd_of_input, coneRd_lt (ReadsBack) : coneRd z w -> z < w ;  coneRtg_le (ReadsBack) : ReflTransGen coneRd z w -> z <= w
--   coneRtg_inCone (ReadsBack) : ReflTransGen coneRd w b -> n <= w -> w ne b -> InCone n C (w - n) (b - n)
--   inCone_coneRtg : InCone n C k i -> ReflTransGen coneRd (n + k) (n + i)
--   coneSet_iff_rtg (ReadsBack, j < len) : i in coneSet n C j iff i < C.gates.length and ReflTransGen coneRd (n + i) (n + j)
--   coneRd_reach_iff (ReadsBack, j < len, w ne n + j) : ReflTransGen coneRd w (n + j) iff exists i in coneSet n C j, w in (gateAt C i).inputs
-- Use: inCone_iff to unfold one level, mem_coneSet to move between coneSet and InCone, cone_agree to compare a gate at two inputs.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega

theorem cones_length (n : ℕ) (C : Circuit) :
    (PEqualNP.EdgeOwnership.cones n C).length = C.gates.length := by
  unfold PEqualNP.EdgeOwnership.cones
  rw [cones_len]; simp

theorem cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    PEqualNP.EdgeOwnership.InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ PEqualNP.EdgeOwnership.InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold PEqualNP.EdgeOwnership.InCone PEqualNP.EdgeOwnership.cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

theorem inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

theorem inCone_of_read (n : ℕ) (C : Circuit) (k j : ℕ) (hj : j < C.gates.length) (hk : k < j)
    (hin : n + k ∈ (gateAt C j).inputs) : PEqualNP.EdgeOwnership.InCone n C k j :=
  (inCone_iff n C k j).mpr ⟨hj, k, hk, hin, Or.inl rfl⟩

theorem inCone_trans (n : ℕ) (C : Circuit) (i k : ℕ) (hik : PEqualNP.EdgeOwnership.InCone n C i k) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C k j → PEqualNP.EdgeOwnership.InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    rw [inCone_iff]
    refine ⟨h0, k', hk', hin, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hik
    · exact ih k' hk' h3

theorem inCone_irrefl (n : ℕ) (C : Circuit) (j : ℕ) : ¬ PEqualNP.EdgeOwnership.InCone n C j j := by
  intro h
  have := (inCone_lt n C j j h).1
  omega

theorem mem_coneSet (n : ℕ) (C : Circuit) (i j : ℕ) :
    i ∈ PEqualNP.Core.coneSet n C j ↔ i = j ∨ PEqualNP.EdgeOwnership.InCone n C i j := by
  unfold PEqualNP.Core.coneSet
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · have := inCone_lt n C i j h
      exact Or.inr ⟨by omega, h⟩

theorem self_mem_coneSet (n : ℕ) (C : Circuit) (j : ℕ) : j ∈ PEqualNP.Core.coneSet n C j :=
  (mem_coneSet n C j j).mpr (Or.inl rfl)

theorem coneSet_mono (n : ℕ) (C : Circuit) (k j : ℕ) (h : PEqualNP.EdgeOwnership.InCone n C k j) :
    PEqualNP.Core.coneSet n C k ⊆ PEqualNP.Core.coneSet n C j := by
  intro i hi
  rw [mem_coneSet] at hi ⊢
  right
  rcases hi with hi | hi
  · rw [hi]; exact h
  · exact inCone_trans n C i k hi j h

theorem coneSet_le (n : ℕ) (C : Circuit) (i j : ℕ) (h : i ∈ PEqualNP.Core.coneSet n C j) : i ≤ j := by
  rw [mem_coneSet] at h
  rcases h with h | h
  · omega
  · have := (inCone_lt n C i j h).1
    omega

theorem coneSet_sub_range (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.Core.coneSet n C j ⊆ Finset.range C.gates.length := by
  intro i hi
  have := coneSet_le n C i j hi
  rw [Finset.mem_range]
  omega

def coneLeaves (n : ℕ) (C : Circuit) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun t => ∃ i ∈ PEqualNP.Core.coneSet n C j, t.val ∈ (gateAt C i).inputs

theorem mem_coneLeaves (n : ℕ) (C : Circuit) (j : ℕ) (t : Fin n) :
    t ∈ coneLeaves n C j ↔ ∃ i ∈ PEqualNP.Core.coneSet n C j, t.val ∈ (gateAt C i).inputs := by
  unfold coneLeaves
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem coneLeaves_mono (n : ℕ) (C : Circuit) (k j : ℕ) (h : PEqualNP.EdgeOwnership.InCone n C k j) :
    coneLeaves n C k ⊆ coneLeaves n C j := by
  intro t ht
  rw [mem_coneLeaves] at ht ⊢
  obtain ⟨i, hi, hti⟩ := ht
  exact ⟨i, coneSet_mono n C k j h hi, hti⟩

theorem cone_agree (n : ℕ) (C : Circuit) (x x' : Fin n → Bool) :
    ∀ j, (∀ t ∈ coneLeaves n C j, x t = x' t) →
      val C (List.ofFn x) (n + j) = val C (List.ofFn x') (n + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hxx
    by_cases hj : j < C.gates.length
    · rw [val_gate (n := n) (by simp) hj, val_gate (n := n) (by simp) hj]
      congr 1
      apply List.map_congr_left
      intro w hw
      by_cases hlt : w < n + j
      · rw [if_pos hlt, if_pos hlt]
        by_cases hwn : w < n
        · rw [val_ofFn_lt C x w hwn, val_ofFn_lt C x' w hwn]
          apply hxx
          rw [mem_coneLeaves]
          exact ⟨j, self_mem_coneSet n C j, hw⟩
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < j := by omega
          apply ih k hk
          intro t ht
          exact hxx t (coneLeaves_mono n C k j (inCone_of_read n C k j hj hk hw) ht)
      · rw [if_neg hlt, if_neg hlt]
    · rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]

theorem cone_agree_gateVal (n : ℕ) (C : Circuit) (x x' : Fin n → Bool) (j : ℕ)
    (hxx : ∀ t ∈ coneLeaves n C j, x t = x' t) :
    PEqualNP.EdgeOwnership.gateVal n C j x = PEqualNP.EdgeOwnership.gateVal n C j x' :=
  cone_agree n C x x' j hxx

def coneRd (n : ℕ) (C : Circuit) (z w : ℕ) : Prop :=
  n ≤ w ∧ w < n + C.gates.length ∧ z ∈ (gateAt C (w - n)).inputs

theorem coneRd_of_input {n : ℕ} {C : Circuit} {t w : ℕ} (ht : t < C.gates.length)
    (hw : w ∈ (gateAt C t).inputs) : coneRd n C w (n + t) :=
  ⟨by omega, by omega, by rw [Nat.add_sub_cancel_left]; exact hw⟩

theorem coneRd_lt {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {z w : ℕ} (h : coneRd n C z w) :
    z < w := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hRB (w - n) (by omega) z h3
  omega

theorem coneRtg_le {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {z w : ℕ}
    (h : Relation.ReflTransGen (coneRd n C) z w) : z ≤ w := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => have := coneRd_lt hRB hbc; omega

theorem coneRtg_inCone {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (w b : ℕ)
    (h : Relation.ReflTransGen (coneRd n C) w b) :
    n ≤ w → w ≠ b → PEqualNP.EdgeOwnership.InCone n C (w - n) (b - n) := by
  induction h with
  | refl => intro _ h; exact absurd rfl h
  | @tail b c hab hbc ih =>
    intro hw _
    have hbn : b < c := coneRd_lt hRB hbc
    have hwb : w ≤ b := coneRtg_le hRB hab
    obtain ⟨h1, h2, h3⟩ := hbc
    rw [inCone_iff]
    refine ⟨by omega, b - n, by omega, ?_, ?_⟩
    · have e : n + (b - n) = b := by omega
      rw [e]; exact h3
    · by_cases hwb' : w = b
      · left; rw [hwb']
      · right; exact ih hw hwb'

theorem inCone_coneRtg {n : ℕ} {C : Circuit} : ∀ i k, PEqualNP.EdgeOwnership.InCone n C k i →
    Relation.ReflTransGen (coneRd n C) (n + k) (n + i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro k h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    have hst : coneRd n C (n + k') (n + i) := coneRd_of_input h0 hin
    rcases h3 with rfl | h3
    · exact Relation.ReflTransGen.single hst
    · exact (ih k' hk' k h3).tail hst

theorem coneSet_iff_rtg {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length)
    (i : ℕ) : i ∈ PEqualNP.Core.coneSet n C j ↔
      i < C.gates.length ∧ Relation.ReflTransGen (coneRd n C) (n + i) (n + j) := by
  rw [mem_coneSet]
  constructor
  · rintro (rfl | hc)
    · exact ⟨hj, Relation.ReflTransGen.refl⟩
    · exact ⟨by have := inCone_lt n C i j hc; omega, inCone_coneRtg j i hc⟩
  · rintro ⟨_, hr⟩
    by_cases hij : i = j
    · left; exact hij
    · right
      have := coneRtg_inCone hRB (n + i) (n + j) hr (by omega) (by omega)
      simpa using this

theorem coneRd_reach_iff {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ}
    (hj : j < C.gates.length) (w : ℕ) (hw : w ≠ n + j) :
    Relation.ReflTransGen (coneRd n C) w (n + j) ↔
      ∃ i ∈ PEqualNP.Core.coneSet n C j, w ∈ (gateAt C i).inputs := by
  constructor
  · intro h
    rcases h.cases_head with h | ⟨c, hc, hcJ⟩
    · exact absurd h hw
    · refine ⟨c - n, ?_, hc.2.2⟩
      rw [coneSet_iff_rtg hRB hj]
      refine ⟨by have := hc.2.1; omega, ?_⟩
      have e : n + (c - n) = c := by have := hc.1; omega
      rw [e]; exact hcJ
  · rintro ⟨i, hiK, hwi⟩
    have hh := (coneSet_iff_rtg hRB hj i).mp hiK
    exact Relation.ReflTransGen.head (coneRd_of_input hh.1 hwi) hh.2

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

-- FRAGMENT live    DEPENDS: fold mono cones restrict
-- Liveness (PEqualNP.FactorSubst.liveGates / liveSize): the gates in the cone of the output gate, and the live
-- circuit liveCirc n C = C restricted to them (frag restrict with S = deadSet), from row 3312.
-- Abbreviation: LG = PEqualNP.FactorSubst.liveGates n C, LS = PEqualNP.FactorSubst.liveSize n C = LG.card.
-- Exports:
--   mem_liveGates : j in LG iff j < C.gates.length and n <= C.output and (j = C.output - n or InCone n C j (C.output - n))
--   def deadSet n C := (Finset.range C.gates.length).filter (not in LG) ;  mem_deadSet : j in deadSet iff j < len and j not in LG
--   live_closed (ReadsBack n C) : the read-closure hypothesis hcl of frag restrict for S = deadSet n C
--   keepL_dead_mem : j in keepL (deadSet n C) C.gates.length iff j in LG
--   dead_size : (Dg n C (deadSet n C) C.gates.length).length = LS
--   liveSize_zero (not (n <= C.output and C.output - n < len)) : LS = 0
--   liveSize_le : LS <= C.gates.length ;  output_live (n <= C.output < n + len) : C.output - n in LG
--   def liveCirc n C : if the output is a gate then (Dg n C deadSet len, output n + rk deadSet (C.output - n)) else ([], C.output)
--   liveCirc_isAO2 : IsAO2 n C -> IsAO2 n (liveCirc n C) ;  liveCirc_size : (liveCirc n C).size = LS
--   liveCirc_val (IsAO2 n C) x : CleanedNonEdge.wireVal n (liveCirc n C) (liveCirc n C).output x = wireVal n C C.output x
--   liveCirc_fun (IsAO2 n C) : circuitFun n (liveCirc n C) = circuitFun n C
--   liveCirc_gate (j < (liveCirc n C).gates.length) : exists i in LG, gateAt (liveCirc n C) j = mkG n C (deadSet n C) i
-- Use: liveCirc gives a circuit of size liveSize computing the same function (rows asking for D.size = liveSize);
-- for a hypothesis about LG elements use mem_liveGates with the cones lemmas (inCone_iff, inCone_trans).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem mem_liveGates (n : ℕ) (C : Circuit) (j : ℕ) :
    j ∈ PEqualNP.FactorSubst.liveGates n C ↔ j < C.gates.length ∧ n ≤ C.output ∧
      (j = C.output - n ∨ PEqualNP.EdgeOwnership.InCone n C j (C.output - n)) := by
  unfold PEqualNP.FactorSubst.liveGates
  rw [Finset.mem_filter, Finset.mem_range]

def deadSet (n : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => j ∉ PEqualNP.FactorSubst.liveGates n C)

theorem mem_deadSet (n : ℕ) (C : Circuit) (j : ℕ) :
    j ∈ deadSet n C ↔ j < C.gates.length ∧ j ∉ PEqualNP.FactorSubst.liveGates n C := by
  unfold deadSet
  rw [Finset.mem_filter, Finset.mem_range]

theorem live_closed (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) :
    ∀ k < C.gates.length, k ∉ deadSet n C →
      ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ deadSet n C := by
  intro k hk hkS i hi
  have hkL : k ∈ PEqualNP.FactorSubst.liveGates n C := by
    by_contra hno
    exact hkS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hno⟩)
  by_cases hin : i < n
  · exact Or.inl hin
  · right
    intro hd
    apply (Finset.mem_filter.mp hd).2
    obtain ⟨_, hno, hc⟩ := (mem_liveGates n C k).mp hkL
    have hilt : i < n + k := hRB k hk i hi
    have hc1 : PEqualNP.EdgeOwnership.InCone n C (i - n) k :=
      inCone_of_read n C (i - n) k hk (by omega)
        (by rw [show n + (i - n) = i by omega]; exact hi)
    rw [mem_liveGates]
    refine ⟨by omega, hno, Or.inr ?_⟩
    rcases hc with e | e
    · rw [← e]; exact hc1
    · exact inCone_trans n C (i - n) k hc1 _ e

theorem keepL_dead_mem (n : ℕ) (C : Circuit) (j : ℕ) :
    j ∈ keepL (deadSet n C) C.gates.length ↔ j ∈ PEqualNP.FactorSubst.liveGates n C := by
  constructor
  · intro h
    have h' := List.mem_filter.mp h
    have hj : j < C.gates.length := List.mem_range.mp h'.1
    have hd : j ∉ deadSet n C := by
      intro hd
      have h2 := h'.2
      simp [hd] at h2
    by_contra hno
    exact hd (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hno⟩)
  · intro h
    have hj : j < C.gates.length := ((mem_liveGates n C j).mp h).1
    have hd : j ∉ deadSet n C := fun hd => (Finset.mem_filter.mp hd).2 h
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hj, ?_⟩
    simp [hd]

theorem dead_size (n : ℕ) (C : Circuit) :
    (Dg n C (deadSet n C) C.gates.length).length = PEqualNP.FactorSubst.liveSize n C := by
  rw [Dg_len]
  unfold rk PEqualNP.FactorSubst.liveSize
  have hnd : (keepL (deadSet n C) C.gates.length).Nodup := List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext j
  rw [List.mem_toFinset]
  exact keepL_dead_mem n C j

theorem liveSize_le (n : ℕ) (C : Circuit) : PEqualNP.FactorSubst.liveSize n C ≤ C.gates.length := by
  unfold PEqualNP.FactorSubst.liveSize PEqualNP.FactorSubst.liveGates
  exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])

theorem output_live (n : ℕ) (C : Circuit) (h1 : n ≤ C.output) (h2 : C.output < n + C.gates.length) :
    C.output - n ∈ PEqualNP.FactorSubst.liveGates n C :=
  (mem_liveGates n C _).mpr ⟨by omega, h1, Or.inl rfl⟩

theorem liveSize_zero (n : ℕ) (C : Circuit)
    (h : ¬ (n ≤ C.output ∧ C.output - n < C.gates.length)) :
    PEqualNP.FactorSubst.liveSize n C = 0 := by
  unfold PEqualNP.FactorSubst.liveSize
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro j hj
  obtain ⟨hj1, hno, hc⟩ := (mem_liveGates n C j).mp hj
  rcases hc with e | e
  · exact h ⟨hno, by omega⟩
  · exact h ⟨hno, (inCone_lt n C j _ e).2⟩

def liveCirc (n : ℕ) (C : Circuit) : Circuit :=
  if n ≤ C.output ∧ C.output - n < C.gates.length then
    ⟨Dg n C (deadSet n C) C.gates.length, n + rk (deadSet n C) (C.output - n)⟩
  else ⟨[], C.output⟩

theorem liveCirc_gate (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < (liveCirc n C).gates.length) :
    ∃ i ∈ PEqualNP.FactorSubst.liveGates n C, gateAt (liveCirc n C) j = mkG n C (deadSet n C) i := by
  unfold liveCirc at hj ⊢
  split_ifs at hj ⊢ with hc
  · have hj' : j < ((keepL (deadSet n C) C.gates.length).map (mkG n C (deadSet n C))).length := hj
    rw [List.length_map] at hj'
    refine ⟨(keepL (deadSet n C) C.gates.length)[j],
      (keepL_dead_mem n C _).mp (List.getElem_mem hj'), ?_⟩
    show (Dg n C (deadSet n C) C.gates.length).getD j ⟨GateOp.or, []⟩ = _
    unfold Dg
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj'), List.getElem_map]
  · exact absurd hj (by simp)

theorem liveCirc_isAO2 (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.TopForm.IsAO2 n (liveCirc n C) := by
  obtain ⟨hao, hRB, h2⟩ := hAO
  unfold liveCirc
  split_ifs with hc
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      have hg' : g ∈ (keepL (deadSet n C) C.gates.length).map (mkG n C (deadSet n C)) := hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
      exact hao (gateAt C j) (keep_gate C _ j hj)
    · exact restrict_rb n C _ hRB (live_closed n C hRB) _ le_rfl
    · intro g hg
      have hg' : g ∈ (keepL (deadSet n C) C.gates.length).map (mkG n C (deadSet n C)) := hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
      have := h2 _ (keep_gate C _ j hj)
      show ((gateAt C j).inputs.map (rn n (deadSet n C))).length = 2
      rw [List.length_map]
      exact this
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      exact absurd hg (by simp)
    · intro j hj
      exact absurd hj (by simp)
    · intro g hg
      exact absurd hg (by simp)

theorem liveCirc_size (n : ℕ) (C : Circuit) :
    (liveCirc n C).size = PEqualNP.FactorSubst.liveSize n C := by
  unfold liveCirc
  split_ifs with hc
  · exact dead_size n C
  · rw [liveSize_zero n C hc]
    rfl

theorem liveCirc_val (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.wireVal n (liveCirc n C) (liveCirc n C).output x =
      PEqualNP.CleanedNonEdge.wireVal n C C.output x := by
  have hRB := hAO.2.1
  unfold liveCirc
  split_ifs with hc
  · obtain ⟨hno, hlt⟩ := hc
    have hoL : C.output - n ∉ deadSet n C := fun hd =>
      (Finset.mem_filter.mp hd).2 ((mem_liveGates n C _).mpr ⟨hlt, hno, Or.inl rfl⟩)
    have h := (restrict_val n C (deadSet n C) hRB (live_closed n C hRB) (List.ofFn x) (by simp)
      C.gates.length le_rfl).2 C.output (by omega) (Or.inr hoL)
    have e3 : rn n (deadSet n C) C.output = n + rk (deadSet n C) (C.output - n) := by
      unfold rn
      rw [if_neg (by omega)]
    rw [e3] at h
    exact h
  · show (List.ofFn x).getD C.output false = (W C.gates (List.ofFn x)).getD C.output false
    by_cases hlt : C.output < n
    · rw [W_prefix C.gates (List.ofFn x) C.output (by rw [List.length_ofFn]; exact hlt)]
    · have h1 : n + C.gates.length ≤ C.output := by
        by_contra h0
        exact hc ⟨by omega, by omega⟩
      rw [getD_ge _ _ (by rw [List.length_ofFn]; omega),
        W_ge C.gates (List.ofFn x) C.output (by rw [List.length_ofFn]; omega)]

theorem liveCirc_fun (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) :
    circuitFun n (liveCirc n C) = circuitFun n C := by
  funext x
  exact liveCirc_val n C hAO x

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

theorem sa_val {m : ℕ} (k : Fin (m + 1)) (v : Fin m) :
    (k.succAbove v).val = if v.val < k.val then v.val else v.val + 1 := by
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt k v (by rw [Fin.lt_def, Fin.coe_castSucc]; exact h)]
    simp
  · rw [Fin.succAbove_of_le_castSucc k v (by rw [Fin.le_def, Fin.coe_castSucc]; omega)]
    simp

theorem simp_out (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    (ev_simp op m ins).2 = Sum.inr m ∨ (∃ c, (ev_simp op m ins).2 = Sum.inl c) ∨
      (ev_simp op m ins).2 ∈ ins := by
  cases op <;> simp only [ev_simp]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try rcases a with (_ | _) | a) <;>
      (try rcases b with (_ | _) | b) <;> simp [ev_simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try rcases a with (_ | _) | a) <;>
      (try rcases b with (_ | _) | b) <;> simp [ev_simpOr]
  · rcases ins with _ | ⟨a, l⟩ <;> (try rcases a with (_ | _) | a) <;> simp [ev_simpNot]
  · simp
  · simp

theorem simp_gate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (ev_simp op m ins).1, ∀ j ∈ g.inputs, Sum.inr j ∈ ins := by
  intro g hg j hj
  cases op <;> simp only [ev_simp] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try rcases a with (_ | _) | a) <;>
      (try rcases b with (_ | _) | b) <;> simp [ev_simpAnd] at hg <;> subst hg <;> simp at hj ⊢ <;>
      omega
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try rcases a with (_ | _) | a) <;>
      (try rcases b with (_ | _) | b) <;> simp [ev_simpOr] at hg <;> subst hg <;> simp at hj ⊢ <;>
      omega
  · rcases ins with _ | ⟨a, l⟩ <;> (try rcases a with (_ | _) | a) <;> simp [ev_simpNot] at hg <;>
      subst hg <;> simp at hj ⊢ <;> omega
  · simp at hg
  · simp at hg

def tau (K j : ℕ) : ℕ := if j < K then j else j + 1

def RI (M K : ℕ) (P : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  (∀ i j, acc.1.getD i (Sum.inl false) = Sum.inr j → j < M → i = tau K j ∨ ∃ g ∈ P, tau K j ∈ g.inputs) ∧
  (∀ g ∈ acc.2, ∀ j ∈ g.inputs, j < M → ∃ g' ∈ P, tau K j ∈ g'.inputs)

theorem ri_step (M K : ℕ) (P : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
    (h : RI M K P acc) : RI M K (P ++ [g]) (ev_elimStep M acc g) := by
  obtain ⟨h1, h2⟩ := h
  have hP : ∀ g' ∈ P, g' ∈ P ++ [g] := fun g' hg' => List.mem_append_left _ hg'
  have hins : ∀ j, Sum.inr j ∈ g.inputs.map (fun i => acc.1.getD i (Sum.inl false)) → j < M →
      ∃ g' ∈ P ++ [g], tau K j ∈ g'.inputs := by
    intro j hj hjM
    obtain ⟨i, hi, hie⟩ := List.mem_map.1 hj
    rcases h1 i j hie hjM with e | ⟨g', hg', hr⟩
    · exact ⟨g, List.mem_append_right _ (List.mem_singleton_self _), e ▸ hi⟩
    · exact ⟨g', hP g' hg', hr⟩
  refine ⟨?_, ?_⟩
  · intro i j hij hjM
    simp only [ev_elimStep] at hij
    by_cases hlt : i < acc.1.length
    · rw [ev_getD_snoc_lt _ _ _ _ hlt] at hij
      rcases h1 i j hij hjM with e | ⟨g', hg', hr⟩
      · exact Or.inl e
      · exact Or.inr ⟨g', hP g' hg', hr⟩
    · by_cases heq : i = acc.1.length
      · rw [ev_getD_snoc_eq _ _ _ _ heq] at hij
        right
        rcases simp_out g.op (M + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
          with e | ⟨c, e⟩ | e
        · rw [e] at hij
          cases hij
          omega
        · rw [e] at hij
          cases hij
        · rw [hij] at e
          exact hins j e hjM
      · rw [ev_getD_snoc_ne _ _ _ _ heq, List.getD_eq_default _ _ (by omega)] at hij
        cases hij
  · intro g' hg' j hj hjM
    simp only [ev_elimStep] at hg'
    rcases List.mem_append.1 hg' with h3 | h3
    · obtain ⟨g'', hg'', hr⟩ := h2 g' h3 j hj hjM
      exact ⟨g'', hP g'' hg'', hr⟩
    · have h4 : g' ∈ (ev_simp g.op (M + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 := by
        simpa using h3
      exact hins j (simp_gate _ _ _ g' h4 j hj) hjM

theorem ri_pass (M K : ℕ) : ∀ (gs P : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate),
    RI M K P acc → RI M K (P ++ gs) (ev_elimPass M gs acc) := by
  intro gs
  induction gs with
  | nil => intro P acc h; rw [List.append_nil]; exact h
  | cons g gs ih =>
    intro P acc h
    rw [ev_elimPass_cons]
    have := ih (P ++ [g]) _ (ri_step M K P acc g h)
    simpa using this

def initR (N K : ℕ) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin N =>
    if i.val < K then Sum.inr i.val else if i.val = K then Sum.inl false else Sum.inr (i.val - 1)

theorem initR_len (N K : ℕ) : (initR N K).length = N := by
  rw [initR, List.length_ofFn]

theorem initR_getD (N K i : ℕ) (hi : i < N) :
    (initR N K).getD i (Sum.inl false) =
      if i < K then Sum.inr i else if i = K then Sum.inl false else Sum.inr (i - 1) := by
  rw [initR, ev_ofFn_getD_lt _ _ _ hi]

theorem ri_init (N M K : ℕ) (hK : K < N) : RI M K [] (initR N K, []) := by
  refine ⟨?_, ?_⟩
  · intro i j hij hjM
    left
    by_cases hi : i < N
    · rw [initR_getD N K i hi] at hij
      split_ifs at hij with h1 h2
      · cases hij
        unfold tau
        split_ifs <;> omega
      · cases hij
        unfold tau
        split_ifs <;> omega
    · rw [List.getD_eq_default _ _ (by rw [initR_len]; omega)] at hij
      cases hij
  · intro g hg
    simp at hg

theorem inv_init (n m : ℕ) (k : Fin (n + 1)) (u : Fin n) (v : Fin m) :
    ev_Inv (n + m) (PEqualNP.Represents.oneEach u v) (PEqualNP.Represents.oneEach (k.succAbove u) v)
      (initR (n + 1 + m) k.val, []) := by
  have hk := k.isLt
  have hu := u.isLt
  have hv := v.isLt
  have hsa := sa_val k u
  refine ⟨oe_len n m u v, by rw [initR_len, oe_len], ?_⟩
  intro i
  by_cases hi : i < n + 1 + m
  · rw [initR_getD _ _ i hi]
    split_ifs with h1 h2
    · refine ⟨by simp only [ev_statValid]; omega, ?_⟩
      show (PEqualNP.Represents.oneEach u v).getD i false = _
      rw [Bool.eq_iff_iff, oe_getD, oe_getD, hsa]
      split_ifs <;> omega
    · refine ⟨trivial, ?_⟩
      show false = _
      symm
      rw [← Bool.not_eq_true, oe_getD, hsa]
      split_ifs <;> omega
    · refine ⟨by simp only [ev_statValid]; omega, ?_⟩
      show (PEqualNP.Represents.oneEach u v).getD (i - 1) false = _
      rw [Bool.eq_iff_iff, oe_getD, oe_getD, hsa]
      split_ifs <;> omega
  · rw [List.getD_eq_default _ _ (by rw [initR_len]; omega)]
    refine ⟨trivial, ?_⟩
    show false = _
    rw [List.getD_eq_default _ _ (by rw [oe_len]; omega)]

def st (M : ℕ) (gs : List Gate) (a0 : List (Bool ⊕ ℕ) × List Gate) (t : ℕ) :
    List (Bool ⊕ ℕ) × List Gate := ev_elimPass M (gs.take t) a0

theorem st_succ (M : ℕ) (gs : List Gate) (a0 : List (Bool ⊕ ℕ) × List Gate) (t : ℕ)
    (ht : t < gs.length) : st M gs a0 (t + 1) = ev_elimStep M (st M gs a0 t) gs[t] := by
  unfold st
  rw [List.take_succ, List.getElem?_eq_getElem ht, ev_elimPass_append]
  rfl

theorem st_len1 (M : ℕ) (gs : List Gate) (a0 : List (Bool ⊕ ℕ) × List Gate) (t : ℕ)
    (ht : t ≤ gs.length) : (st M gs a0 t).1.length = a0.1.length + t := by
  unfold st
  rw [ev_elimPass_fst_len, List.length_take]
  omega

theorem st_stable (M : ℕ) (gs : List Gate) (a0 : List (Bool ⊕ ℕ) × List Gate) (t t' i : ℕ)
    (htt : t ≤ t') (ht' : t' ≤ gs.length) (hi : i < (st M gs a0 t).1.length) :
    (st M gs a0 t').1.getD i (Sum.inl false) = (st M gs a0 t).1.getD i (Sum.inl false) := by
  have e : gs.take t' = gs.take t ++ (gs.drop t).take (t' - t) := by
    conv_lhs => rw [show t' = t + (t' - t) by omega]
    rw [List.take_add]
  unfold st at hi ⊢
  rw [e, ev_elimPass_append, ev_elimPass_getD_lt _ _ _ _ _ hi]

theorem st_count (M : ℕ) (gs : List Gate) (a0 : List (Bool ⊕ ℕ) × List Gate) (j0 j1 : ℕ)
    (h01 : j0 < j1) (hj1 : j1 < gs.length)
    (hn0 : (ev_simp gs[j0].op (M + (st M gs a0 j0).2.length)
      (gs[j0].inputs.map fun i => (st M gs a0 j0).1.getD i (Sum.inl false))).1 = none)
    (hn1 : (ev_simp gs[j1].op (M + (st M gs a0 j1).2.length)
      (gs[j1].inputs.map fun i => (st M gs a0 j1).1.getD i (Sum.inl false))).1 = none) :
    (ev_elimPass M gs a0).2.length + 2 ≤ a0.2.length + gs.length := by
  have key : ∀ t, t ≤ gs.length → (st M gs a0 t).2.length + (if j0 < t then 1 else 0) +
      (if j1 < t then 1 else 0) ≤ a0.2.length + t := by
    intro t
    induction t with
    | zero => intro _; simp [st, ev_elimPass]
    | succ t ih =>
      intro ht
      have ih' := ih (by omega)
      rw [st_succ M gs a0 t (by omega)]
      simp only [ev_elimStep, List.length_append]
      by_cases e0 : t = j0
      · subst e0
        have hl : (gs[t].inputs.map fun i => (st M gs a0 t).1.getD i (Sum.inl false)) =
            (gs[t].inputs.map fun i => (st M gs a0 t).1.getD i (Sum.inl false)) := rfl
        rw [hn0]
        simp only [Option.toList_none, List.length_nil]
        split_ifs at ih' ⊢ <;> omega
      · by_cases e1 : t = j1
        · subst e1
          rw [hn1]
          simp only [Option.toList_none, List.length_nil]
          split_ifs at ih' ⊢ <;> omega
        · have := ev_toList_len_le (ev_simp gs[t].op (M + (st M gs a0 t).2.length)
            (gs[t].inputs.map fun i => (st M gs a0 t).1.getD i (Sum.inl false))).1
          split_ifs at ih' ⊢ <;> omega
  have := key gs.length le_rfl
  have e : st M gs a0 gs.length = ev_elimPass M gs a0 := by unfold st; rw [List.take_length]
  rw [e] at this
  split_ifs at this <;> omega

def idx (s : Bool ⊕ ℕ) : ℕ := Sum.elim (fun _ => 0) id s

def gg (gs : List Gate) (j : ℕ) : Gate := gs.getD j ⟨GateOp.or, []⟩

theorem gg_eq (gs : List Gate) (j : ℕ) (hj : j < gs.length) : gg gs j = gs[j] := by
  unfold gg
  rw [List.getD_eq_getElem _ _ hj]

theorem simp_inr (op : GateOp) (mm : ℕ) (l : List ℕ) (f : ℕ → Bool ⊕ ℕ)
    (hf : ∀ i ∈ l, ∃ a, f i = Sum.inr a)
    (hop : ((op = GateOp.and ∨ op = GateOp.or) ∧ l.length = 2) ∨ (op = GateOp.not ∧ l.length = 1)) :
    ev_simp op mm (l.map f) = (some ⟨op, l.map (fun i => idx (f i))⟩, Sum.inr mm) := by
  rcases hop with ⟨hop, hl⟩ | ⟨hop, hl⟩
  · obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hl
    obtain ⟨x, hx⟩ := hf a (by simp)
    obtain ⟨y, hy⟩ := hf b (by simp)
    simp only [List.map_cons, List.map_nil, hx, hy]
    rcases hop with rfl | rfl <;> rfl
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hl
    obtain ⟨x, hx⟩ := hf a (by simp)
    simp only [List.map_cons, List.map_nil, hx]
    subst hop
    rfl

theorem two_idx (l : List Gate) (p : Gate → Bool) (i j : ℕ) (hij : i < j) (hj : j < l.length)
    (hpi : p (l[i]'(by omega)) = true) (hpj : p l[j] = true) : 2 ≤ (l.filter p).length := by
  have e : l = l.take (i + 1) ++ l.drop (i + 1) := (List.take_append_drop _ _).symm
  rw [e, List.filter_append, List.length_append]
  have h1 : 0 < ((l.take (i + 1)).filter p).length := by
    apply List.length_pos_of_mem (a := l[i]'(by omega))
    rw [List.mem_filter]
    refine ⟨?_, hpi⟩
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp; omega, by simp⟩
  have h2 : 0 < ((l.drop (i + 1)).filter p).length := by
    apply List.length_pos_of_mem (a := l[j])
    rw [List.mem_filter]
    refine ⟨?_, hpj⟩
    rw [List.mem_iff_getElem]
    exact ⟨j - (i + 1), by simp; omega, by simp; congr 1; omega⟩
  omega

theorem copy_inv (M N k : ℕ) (gs : List Gate) (hk : k < N)
    (hRB : ∀ j, j < gs.length → ∀ i ∈ (gg gs j).inputs, i < N + j)
    (hred : ∀ j, j < gs.length → (((gg gs j).op = GateOp.and ∨ (gg gs j).op = GateOp.or) ∧
      (gg gs j).inputs.length = 2) ∨ ((gg gs j).op = GateOp.not ∧ (gg gs j).inputs.length = 1))
    (j0 w : ℕ) (hj0 : j0 < gs.length) (hw : w ≠ k)
    (hg0 : gg gs j0 = ⟨GateOp.or, [k, w]⟩ ∨ gg gs j0 = ⟨GateOp.or, [w, k]⟩)
    (honly : ∀ j, j < gs.length → j ≠ j0 → k ∉ (gg gs j).inputs) :
    ∀ t, t ≤ gs.length →
      (∀ i, i < N + t → i ≠ k → ∃ a, (st M gs (initR N k, []) t).1.getD i (Sum.inl false) = Sum.inr a) ∧
      (∀ j, j < t → j ≠ j0 → (⟨(gg gs j).op, (gg gs j).inputs.map
          (fun i => idx ((st M gs (initR N k, []) t).1.getD i (Sum.inl false)))⟩ : Gate) ∈
          (st M gs (initR N k, []) t).2) ∧
      (j0 < t → (st M gs (initR N k, []) t).1.getD (N + j0) (Sum.inl false) =
          (st M gs (initR N k, []) t).1.getD w (Sum.inl false)) := by
  have hlen : ∀ t, t ≤ gs.length → (st M gs (initR N k, []) t).1.length = N + t := by
    intro t ht
    rw [st_len1 _ _ _ _ ht, initR_len]
  have hkst : ∀ t, t ≤ gs.length → (st M gs (initR N k, []) t).1.getD k (Sum.inl false) = Sum.inl false := by
    intro t ht
    rw [st_stable M gs _ 0 t k (by omega) ht (by rw [hlen 0 (by omega)]; omega)]
    show (initR N k).getD k (Sum.inl false) = Sum.inl false
    rw [initR_getD N k k hk, if_neg (by omega), if_pos rfl]
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · intro i hi hik
      show ∃ a, (initR N k).getD i (Sum.inl false) = Sum.inr a
      rw [initR_getD N k i (by omega)]
      split_ifs with h1
      · exact ⟨i, rfl⟩
      · exact ⟨i - 1, rfl⟩
    · intro j hj
      omega
    · intro h
      omega
  | succ t ih =>
    intro ht
    obtain ⟨F2, F3, F4⟩ := ih (by omega)
    have hl := hlen t (by omega)
    set S := fun i => (st M gs (initR N k, []) t).1.getD i (Sum.inl false) with hS
    set r := ev_simp (gg gs t).op (M + (st M gs (initR N k, []) t).2.length) ((gg gs t).inputs.map S) with hr
    have hst : st M gs (initR N k, []) (t + 1) =
        ((st M gs (initR N k, []) t).1 ++ [r.2], (st M gs (initR N k, []) t).2 ++ r.1.toList) := by
      rw [st_succ M gs _ t (by omega), ← gg_eq gs t (by omega)]
      rfl
    have hlt : ∀ i, i < N + t → (st M gs (initR N k, []) (t + 1)).1.getD i (Sum.inl false) = S i := by
      intro i hi
      rw [hst]
      exact ev_getD_snoc_lt _ _ _ _ (by rw [hl]; exact hi)
    have hmap : ∀ j, j ≤ t → (gg gs j).inputs.map
        (fun i => idx ((st M gs (initR N k, []) (t + 1)).1.getD i (Sum.inl false))) =
        (gg gs j).inputs.map (fun i => idx (S i)) := by
      intro j hj
      apply List.map_congr_left
      intro i hi
      rw [hlt i (by have := hRB j (by omega) i hi; omega)]
    by_cases htj : t = j0
    · subst htj
      have hwlt : w < N + t := by
        apply hRB t (by omega)
        rcases hg0 with e | e <;> rw [e] <;> simp
      obtain ⟨a, ha⟩ := F2 w hwlt hw
      have hSk : S k = Sum.inl false := hkst t (by omega)
      have hSw : S w = Sum.inr a := ha
      have hr2 : r = (none, Sum.inr a) := by
        rw [hr]
        rcases hg0 with e | e <;> rw [e] <;> simp only [List.map_cons, List.map_nil] <;>
          rw [hSk, hSw] <;> rfl
      refine ⟨?_, ?_, ?_⟩
      · intro i hi hik
        by_cases hi2 : i < N + t
        · rw [hlt i hi2]
          exact F2 i hi2 hik
        · rw [hst, ev_getD_snoc_eq _ _ _ _ (by rw [hl]; omega), hr2]
          exact ⟨a, rfl⟩
      · intro j hj hjj
        rw [hmap j (by omega), hst, hr2]
        simp only [Option.toList_none, List.append_nil]
        exact F3 j (by omega) hjj
      · intro _
        rw [hlt w hwlt, hst, ev_getD_snoc_eq _ _ _ _ (by rw [hl]), hr2]
        exact ha.symm
    · have hall : ∀ i ∈ (gg gs t).inputs, ∃ a, S i = Sum.inr a := by
        intro i hi
        refine F2 i (hRB t (by omega) i hi) ?_
        intro e
        exact honly t (by omega) htj (e ▸ hi)
      have hr2 : r = (some ⟨(gg gs t).op, (gg gs t).inputs.map (fun i => idx (S i))⟩,
          Sum.inr (M + (st M gs (initR N k, []) t).2.length)) :=
        simp_inr _ _ _ S hall (hred t (by omega))
      refine ⟨?_, ?_, ?_⟩
      · intro i hi hik
        by_cases hi2 : i < N + t
        · rw [hlt i hi2]
          exact F2 i hi2 hik
        · rw [hst, ev_getD_snoc_eq _ _ _ _ (by rw [hl]; omega), hr2]
          exact ⟨_, rfl⟩
      · intro j hj hjj
        rw [hmap j (by omega), hst, hr2]
        simp only [Option.toList_some]
        by_cases hjt : j = t
        · subst hjt
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · exact List.mem_append_left _ (F3 j (by omega) hjj)
      · intro h0
        have hj0t : j0 < t := by omega
        have hwlt : w < N + j0 := by
          apply hRB j0 hj0
          rcases hg0 with e | e <;> rw [e] <;> simp
        rw [hlt (N + j0) (by omega), hlt w (by omega)]
        exact F4 hj0t

theorem reader_of (C : Circuit) (x : ℕ)
    (h : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) x ≠ 0) :
    ∃ j1, j1 < C.gates.length ∧ x ∈ (gg C.gates j1).inputs := by
  unfold PEqualNP.MetaComplexity.NestedCover.readsIn at h
  obtain ⟨j1, hj1, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_range] at hj1
  refine ⟨j1, hj1, ?_⟩
  have hpos : 0 < (gateAt C j1).inputs.count x := Nat.pos_of_ne_zero hc
  exact List.count_pos_iff.1 hpos

def RedG (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = GateOp.not ∧ g.inputs.length = 1)

def Rdc (N : ℕ) (C : Circuit) : Prop :=
  ((∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧
    ReadsBack N C ∧ 0 < C.size ∧ C.output + 1 = N + C.size ∧
    (∀ j < C.size, (readsIn C (Finset.range C.size) (N + j) = 0 ↔ j + 1 = C.size))) ∨
  (C.size = 0 ∧ C.output < N)

theorem cone_reader (N : ℕ) (D : Circuit) (i : ℕ) : ∀ o, PEqualNP.EdgeOwnership.InCone N D i o →
    ∃ i', (i' = o ∨ PEqualNP.EdgeOwnership.InCone N D i' o) ∧ i' < D.gates.length ∧
      N + i ∈ (gateAt D i').inputs := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
    intro h
    obtain ⟨ho, k, hk, hin, hik⟩ := (inCone_iff N D i o).1 h
    rcases hik with rfl | hik
    · exact ⟨o, Or.inl rfl, ho, hin⟩
    · obtain ⟨i', hi', hil, hr⟩ := ih k hk hik
      have hko : PEqualNP.EdgeOwnership.InCone N D k o := inCone_of_read N D k o ho hk hin
      refine ⟨i', Or.inr ?_, hil, hr⟩
      rcases hi' with rfl | hi'
      · exact hko
      · exact inCone_trans N D i' k hi' o hko

theorem rk_surj (S : Finset ℕ) : ∀ m p, p < rk S m → ∃ i, i < m ∧ i ∉ S ∧ rk S i = p := by
  intro m
  induction m with
  | zero => intro p hp; simp [rk, keepL] at hp
  | succ m ih =>
    intro p hp
    by_cases hm : m ∈ S
    · have e : rk S (m + 1) = rk S m := by unfold rk; rw [keepL_succ_in S m hm]
      obtain ⟨i, hi, hiS, he⟩ := ih p (by omega)
      exact ⟨i, by omega, hiS, he⟩
    · rw [rk_succ_out S m hm] at hp
      by_cases hpl : p < rk S m
      · obtain ⟨i, hi, hiS, he⟩ := ih p hpl
        exact ⟨i, by omega, hiS, he⟩
      · exact ⟨m, by omega, hm, by omega⟩

theorem rk_inj (S : Finset ℕ) (i j : ℕ) (hi : i ∉ S) (hj : j ∉ S) (h : rk S i = rk S j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := rk_lt S i j hlt hi
    omega
  · have := rk_lt S j i hlt hj
    omega

theorem rk_empty (m : ℕ) : rk ∅ m = m := by
  unfold rk keepL
  simp

theorem rn_empty (N w : ℕ) : rn N ∅ w = w := by
  unfold rn
  split_ifs with h
  · rfl
  · rw [rk_empty]
    omega

theorem readsIn_zero_iff (C : Circuit) (w : ℕ) :
    readsIn C (Finset.range C.size) w = 0 ↔ ∀ g ∈ C.gates, w ∉ g.inputs := by
  unfold readsIn
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h g hg hw
    obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.1 hg
    have := h q (Finset.mem_range.2 hq)
    rw [gateAt_eq hq] at this
    exact (List.count_pos_iff.2 hw).ne' this
  · intro h q hq
    rw [Finset.mem_range] at hq
    rw [gateAt_eq hq]
    exact List.count_eq_zero.2 (h _ (List.getElem_mem hq))

theorem clean (N : ℕ) (D : Circuit) (hsh : ∀ g ∈ D.gates, RedG g) (hrb : ReadsBack N D)
    (hout : D.output < N + D.gates.length) :
    ∃ E : Circuit, (∀ x : List Bool, x.length = N → E.eval x = D.eval x) ∧ Rdc N E ∧
      E.size ≤ D.size ∧
      (∀ w, w < N → ((∃ g ∈ E.gates, w ∈ g.inputs) ∨ E.output = w) →
        ((∃ g ∈ D.gates, w ∈ g.inputs) ∨ D.output = w)) ∧
      (E.size = D.size → ∀ w, w < N → ((∃ g ∈ D.gates, w ∈ g.inputs) ∨ D.output = w) →
        ((∃ g ∈ E.gates, w ∈ g.inputs) ∨ E.output = w)) := by
  by_cases hoN : D.output < N
  · refine ⟨⟨[], D.output⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      show (W [] x).getD D.output false = (W D.gates x).getD D.output false
      rw [W_prefix D.gates x D.output (by omega)]
      rfl
    · right
      exact ⟨rfl, hoN⟩
    · show 0 ≤ D.gates.length
      omega
    · intro w hw h
      rcases h with ⟨g, hg, _⟩ | h
      · simp at hg
      · exact Or.inr h
    · intro hs w hw h
      have h0 : D.gates.length = 0 := by
        have : (0 : ℕ) = D.gates.length := hs
        omega
      rcases h with ⟨g, hg, _⟩ | h
      · rw [List.length_eq_zero_iff] at h0
        rw [h0] at hg
        simp at hg
      · exact Or.inr h
  · set o := D.output - N with ho
    have hol : o < D.gates.length := by omega
    have hoe : D.output = N + o := by omega
    set S := deadSet N D with hS
    have hcl := live_closed N D hrb
    have hlive : ∀ i, i ∉ S ↔ (i < D.gates.length → (i = o ∨ PEqualNP.EdgeOwnership.InCone N D i o)) := by
      intro i
      rw [hS, mem_deadSet, mem_liveGates]
      constructor
      · intro h hi
        by_contra hc
        exact h ⟨hi, fun hl => hc hl.2.2⟩
      · rintro h ⟨hi, hl⟩
        exact hl ⟨hi, by omega, h hi⟩
    have hoS : o ∉ S := (hlive o).2 (fun _ => Or.inl rfl)
    have hSlt : ∀ j ∈ S, j < D.gates.length := fun j hj => ((mem_deadSet N D j).1 hj).1
    have hgtS : ∀ j, o < j → j < D.gates.length → j ∈ S := by
      intro j hj hjl
      by_contra hjS
      rcases (hlive j).1 hjS hjl with e | e
      · omega
      · have := (inCone_lt N D j o e).1
        omega
    have hrk_tail : ∀ m, o + 1 ≤ m → m ≤ D.gates.length → rk S m = rk S o + 1 := by
      intro m
      induction m with
      | zero => intro h; omega
      | succ m ih =>
        intro h1 h2
        by_cases hm : m = o
        · rw [hm]
          exact rk_succ_out S o hoS
        · have hmS : m ∈ S := hgtS m (by omega) (by omega)
          unfold rk
          rw [keepL_succ_in S m hmS]
          exact ih (by omega) (by omega)
    have hrklen := hrk_tail D.gates.length (by omega) le_rfl
    have hEgates : ∀ g, g ∈ Dg N D S D.gates.length ↔
        ∃ i, i < D.gates.length ∧ i ∉ S ∧ g = mkG N D S i := by
      intro g
      unfold Dg
      rw [List.mem_map]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have := List.mem_filter.1 hi
        simp only [List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at this
        exact ⟨i, this.1, this.2, rfl⟩
      · rintro ⟨i, hi, hiS, rfl⟩
        refine ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi, by simpa using hiS⟩, rfl⟩
    have hrnin : ∀ i, i < D.gates.length → i ∉ S → ∀ x ∈ (gateAt D i).inputs, ∀ w, w < N →
        rn N S x = w → x = w := by
      intro i hi hiS x hx w hw hrx
      unfold rn at hrx
      split_ifs at hrx with h
      · exact hrx
      · omega
    refine ⟨⟨Dg N D S D.gates.length, N + rk S o⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hv := (restrict_val N D S hrb hcl x hx D.gates.length le_rfl).2 D.output hout
        (Or.inr (by rw [← ho]; exact hoS))
      show (W (Dg N D S D.gates.length) x).getD (N + rk S o) false = (W D.gates x).getD D.output false
      rw [hoe, rn_gate] at hv
      rw [hv, hoe]
      rfl
    · left
      have hEsz : (⟨Dg N D S D.gates.length, N + rk S o⟩ : Circuit).size = rk S o + 1 := by
        show (Dg N D S D.gates.length).length = _
        rw [Dg_len, hrklen]
      refine ⟨?_, ?_, by rw [hEsz]; omega,
        by show N + rk S o + 1 = N + (Dg N D S D.gates.length).length; rw [Dg_len, hrklen]; omega, ?_⟩
      · intro g hg
        obtain ⟨i, hi, hiS, rfl⟩ := (hEgates g).1 hg
        have := hsh _ (gateAt_mem hi)
        unfold mkG
        simpa [RedG] using this
      · intro j hj i hii
        exact restrict_rb N D S hrb hcl D.gates.length le_rfl j hj i hii
      · intro p hp
        rw [readsIn_zero_iff, hEsz]
        rw [hEsz] at hp
        constructor
        · intro hz
          by_contra hne
          obtain ⟨i, hi, hiS, hip⟩ := rk_surj S D.gates.length p (by rw [hrklen]; omega)
          have hio : i ≠ o := fun e => hne (by rw [← hip, e])
          rcases (hlive i).1 hiS hi with e | hc
          · exact hio e
          obtain ⟨i', hi', hil, hr⟩ := cone_reader N D i o hc
          have hi'S : i' ∉ S := (hlive i').2 (fun _ => hi')
          apply hz (mkG N D S i') ((hEgates _).2 ⟨i', hil, hi'S, rfl⟩)
          unfold mkG
          rw [List.mem_map]
          exact ⟨N + i, hr, by rw [rn_gate, hip]⟩
        · intro hpo g hg hpg
          obtain ⟨i', hi', hi'S, rfl⟩ := (hEgates g).1 hg
          unfold mkG at hpg
          rw [List.mem_map] at hpg
          obtain ⟨x, hx, hrx⟩ := hpg
          have hxlt := hrb i' hi' x hx
          by_cases hxN : x < N
          · unfold rn at hrx
            rw [if_pos hxN] at hrx
            omega
          · have hxS : x - N ∉ S := (hcl i' hi' hi'S x hx).resolve_left hxN
            unfold rn at hrx
            rw [if_neg hxN] at hrx
            have he : rk S (x - N) = rk S o := by omega
            have := rk_inj S _ _ hxS hoS he
            have hi'o : i' ≤ o := by
              by_contra hc
              exact hi'S (hgtS i' (by omega) hi')
            omega
    · show (Dg N D S D.gates.length).length ≤ D.gates.length
      have := restrict_size N D S hSlt
      omega
    · intro w hw h
      rcases h with ⟨g, hg, hwg⟩ | h
      · obtain ⟨i, hi, hiS, rfl⟩ := (hEgates g).1 hg
        unfold mkG at hwg
        rw [List.mem_map] at hwg
        obtain ⟨x, hx, hrx⟩ := hwg
        have := hrnin i hi hiS x hx w hw hrx
        exact Or.inl ⟨gateAt D i, gateAt_mem hi, this ▸ hx⟩
      · exfalso
        change N + rk S o = w at h
        omega
    · intro hs w hw h
      have hS0 : S = ∅ := by
        have h1 := restrict_size N D S hSlt
        have h2 : (Dg N D S D.gates.length).length = D.gates.length := hs
        rw [h2] at h1
        exact Finset.card_eq_zero.1 (by omega)
      rcases h with ⟨g, hg, hwg⟩ | h
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
        left
        refine ⟨mkG N D S i, (hEgates _).2 ⟨i, hi, by rw [hS0]; simp, rfl⟩, ?_⟩
        unfold mkG
        rw [List.mem_map, gateAt_eq hi]
        exact ⟨w, hwg, by rw [hS0, rn_empty]⟩
      · exfalso
        omega

theorem simp_red (op : GateOp) (mm : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (ev_simp op mm ins).1, RedG g := by
  intro g hg
  cases op <;> simp only [ev_simp] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try rcases a with (_ | _) | a) <;>
      (try rcases b with (_ | _) | b) <;> simp [ev_simpAnd] at hg <;> subst hg <;> simp [RedG]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try rcases a with (_ | _) | a) <;>
      (try rcases b with (_ | _) | b) <;> simp [ev_simpOr] at hg <;> subst hg <;> simp [RedG]
  · rcases ins with _ | ⟨a, l⟩ <;> (try rcases a with (_ | _) | a) <;> simp [ev_simpNot] at hg <;>
      subst hg <;> simp [RedG]
  · simp at hg
  · simp at hg

theorem pass_red (M : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, RedG g) : ∀ g ∈ (ev_elimPass M gs acc).2, RedG g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [ev_elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simp_red _ _ _ g' (by simpa using h1)

theorem sv_mono (a b : ℕ) (s : Bool ⊕ ℕ) (h : a ≤ b) (hs : ev_statValid a s) : ev_statValid b s := by
  cases s with
  | inl c => trivial
  | inr j => simp only [ev_statValid] at hs ⊢; omega

theorem pass_vrb (M : ℕ) (gs : List Gate) (hok : ∀ g ∈ gs, ev_OkGate g) :
    ∀ acc : List (Bool ⊕ ℕ) × List Gate,
      (∀ i, ev_statValid (M + acc.2.length) (acc.1.getD i (Sum.inl false))) → RBo M acc.2 →
      (∀ i, ev_statValid (M + (ev_elimPass M gs acc).2.length) ((ev_elimPass M gs acc).1.getD i (Sum.inl false))) ∧
        RBo M (ev_elimPass M gs acc).2 := by
  induction gs with
  | nil => intro acc h1 h2; exact ⟨h1, h2⟩
  | cons g gs ih =>
    intro acc h1 h2
    rw [ev_elimPass_cons]
    apply ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    · have hg := hok g List.mem_cons_self
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hv : ∀ s ∈ ins, ev_statValid (List.replicate (M + acc.2.length) false).length s := by
        intro s hs
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 hs
        rw [List.length_replicate]
        exact h1 i
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
        have := hg.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
        exact this
      have hsd := (ev_simp_sound g.op hop (List.replicate (M + acc.2.length) false) ins
        (by simp [hins]; exact hg.2) hv).1
      rw [List.length_replicate] at hsd
      intro i
      simp only [ev_elimStep, List.length_append]
      by_cases hlt : i < acc.1.length
      · rw [ev_getD_snoc_lt _ _ _ _ hlt]
        exact sv_mono _ _ _ (by omega) (h1 i)
      · by_cases heq : i = acc.1.length
        · rw [ev_getD_snoc_eq _ _ _ _ heq]
          rw [Nat.add_assoc] at hsd
          exact hsd
        · rw [ev_getD_snoc_ne _ _ _ _ heq, List.getD_eq_default _ _ (by omega)]
          trivial
    · simp only [ev_elimStep]
      apply RBo_append M _ _ h2
      intro p hp i hi
      have hg1 : ∀ g' ∈ (ev_simp g.op (M + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1,
          ∀ j ∈ g'.inputs, j < M + acc.2.length := by
        intro g' hg' j hj
        have hm := simp_gate _ _ _ g' hg' j hj
        obtain ⟨i0, _, hie⟩ := List.mem_map.1 hm
        have := h1 i0
        rw [hie] at this
        exact this
      cases hr : (ev_simp g.op (M + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 with
      | none => rw [hr] at hp; simp at hp
      | some G =>
        rw [hr] at hp hi
        simp at hp
        subst hp
        simp only [Option.toList_some, List.getD_cons_zero] at hi
        have := hg1 G (by rw [hr]; rfl) i hi
        omega

theorem sense_mem (gs : List Gate) (o w : ℕ)
    (h : (∃ g ∈ gs, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ w ∈ g.inputs) ∨
      (g.op = GateOp.not ∧ g.inputs.head? = some w)) ∨ o = w) :
    (∃ g ∈ gs, w ∈ g.inputs) ∨ o = w := by
  rcases h with ⟨g, hg, ⟨_, hw⟩ | ⟨_, hw⟩⟩ | h
  · exact Or.inl ⟨g, hg, hw⟩
  · obtain ⟨t, ht⟩ := List.head?_eq_some_iff.1 hw
    exact Or.inl ⟨g, hg, by rw [ht]; simp⟩
  · exact Or.inr h

theorem mem_sense (gs : List Gate) (o w : ℕ) (hr : ∀ g ∈ gs, RedG g)
    (h : (∃ g ∈ gs, w ∈ g.inputs) ∨ o = w) :
    (∃ g ∈ gs, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ w ∈ g.inputs) ∨
      (g.op = GateOp.not ∧ g.inputs.head? = some w)) ∨ o = w := by
  rcases h with ⟨g, hg, hw⟩ | h
  · left
    refine ⟨g, hg, ?_⟩
    rcases hr g hg with ⟨hop, _⟩ | ⟨hop, hl⟩
    · exact Or.inl ⟨hop, hw⟩
    · obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hl
      rw [hx] at hw ⊢
      simp at hw
      exact Or.inr ⟨hop, by rw [hw]; rfl⟩
  · exact Or.inr h

theorem row_del : ∀ (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (k : Fin (n + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 1 + m) C → 0 < C.size → C.output + 1 = (n + 1 + m) + C.size → (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + 1 + m) + j) = 0 ↔ j + 1 = C.size)) → ((∃ g ∈ C.gates, k.val ∈ g.inputs) ∨ C.output = k.val) → (∃ (u u2 : Fin n) (v v2 : Fin m), A (k.succAbove u) v ≠ A (k.succAbove u2) v2) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ (∀ g ∈ C2.gates, RedG g) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ C2.output < (n + m) + C2.gates.length ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) v) C2 ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (k.succAbove u).val ∈ g.inputs) ∨ C.output = (k.succAbove u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + 1 + v.val) ∈ g.inputs) ∨ C.output = (n + 1 + v.val))) ∧ (C2.size + 2 ≤ C.size ∨ ∀ v : Fin m, ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (n + 1 + v.val) ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some (n + 1 + v.val))) ∨ C.output = (n + 1 + v.val)) → ((∃ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (n + v.val) ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some (n + v.val))) ∨ C2.output = (n + v.val))) := by
  intro n m A k C hF hrep hred hrb hpos hout hreads hread hnc
  have hk := k.isLt
  have hgg : ∀ j, gg C.gates j = gateAt C j := fun j => rfl
  have hRB : ∀ j, j < C.gates.length → ∀ i ∈ (gg C.gates j).inputs, i < n + 1 + m + j := by
    intro j hj i hi
    rw [hgg] at hi
    exact hrb j hj i hi
  have hredg : ∀ j, j < C.gates.length → (((gg C.gates j).op = GateOp.and ∨ (gg C.gates j).op = GateOp.or) ∧
      (gg C.gates j).inputs.length = 2) ∨ ((gg C.gates j).op = GateOp.not ∧ (gg C.gates j).inputs.length = 1) := by
    intro j hj
    rw [gg_eq _ _ hj]
    exact hred _ (List.getElem_mem hj)
  have hnok : ∀ g ∈ C.gates, ev_NOkGate g := by
    intro g hg
    refine ⟨hF g hg, fun hn => ?_⟩
    rcases hred g hg with ⟨hop, _⟩ | ⟨_, hl⟩
    · rcases hop with h | h
      · exact absurd (h.symm.trans hn) (fun e => GateOp.noConfusion e)
      · exact absurd (h.symm.trans hn) (fun e => GateOp.noConfusion e)
    · omega
  have hsz : C.size = C.gates.length := rfl
  have hreadg : ∃ g ∈ C.gates, k.val ∈ g.inputs := by
    rcases hread with h | h
    · exact h
    · exfalso
      rw [hsz] at hout
      omega
  have hk0 : (initR (n + 1 + m) k.val).getD k.val (Sum.inl false) = Sum.inl false := by
    rw [initR_getD _ _ _ (by omega), if_neg (by omega), if_pos rfl]
  set a0 : List (Bool ⊕ ℕ) × List Gate := (initR (n + 1 + m) k.val, []) with ha0
  set acc := ev_elimPass (n + m) C.gates a0 with hacc
  have hacc_st : st (n + m) C.gates a0 C.gates.length = acc := by
    unfold st
    rw [List.take_length]
  have hlen0 : ∀ t, t ≤ C.gates.length → (st (n + m) C.gates a0 t).1.length = n + 1 + m + t := by
    intro t ht
    rw [st_len1 _ _ _ _ ht]
    show (initR (n + 1 + m) k.val).length + t = _
    rw [initR_len]
  have hkst : ∀ t, t ≤ C.gates.length →
      (st (n + m) C.gates a0 t).1.getD k.val (Sum.inl false) = Sum.inl false := by
    intro t ht
    rw [st_stable _ _ _ 0 t _ (by omega) ht (by rw [hlen0 0 (by omega)]; omega)]
    exact hk0
  have hlen1 : acc.2.length + 1 ≤ C.gates.length := by
    have := ev_elimPass_len_lt (n + m) k.val C.gates a0 hnok
      (by show k.val < (initR (n + 1 + m) k.val).length; rw [initR_len]; omega) ⟨false, hk0⟩ hreadg
    rw [← hacc] at this
    have h0 : a0.2.length = 0 := rfl
    omega
  have hval : ∀ (u : Fin n) (v : Fin m),
      ev_statVal (W acc.2 (PEqualNP.Represents.oneEach u v)) (acc.1.getD C.output (Sum.inl false)) =
        A (k.succAbove u) v := by
    intro u v
    have hinv := ev_Inv_pass (n + m) _ C.gates _ _ (fun g hg => hF g hg) (inv_init n m k u v)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2]
    exact hrep (k.succAbove u) v
  have hri := ri_pass (n + m) k.val C.gates [] _ (ri_init (n + 1 + m) (n + m) k.val (by omega))
  rw [← hacc, List.nil_append] at hri
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨u, u2, v, v2, hne⟩ := hnc
    have h1 := hval u v
    have h2 := hval u2 v2
    rw [hst] at h1 h2
    exact absurd (h1.symm.trans h2) hne
  | inr j =>
    have hvr := pass_vrb (n + m) C.gates (fun g hg => hF g hg) a0 (by
      intro i
      rw [ha0]
      show ev_statValid (n + m + 0) ((initR (n + 1 + m) k.val).getD i (Sum.inl false))
      by_cases hi : i < n + 1 + m
      · rw [initR_getD _ _ _ hi]
        split_ifs <;> simp only [ev_statValid] <;> omega
      · rw [List.getD_eq_default _ _ (by rw [initR_len]; omega)]
        trivial) (by rw [ha0]; exact RBo_nil _)
    rw [← hacc] at hvr
    have hjv : j < n + m + acc.2.length := by
      have := hvr.1 C.output
      rw [hst] at this
      exact this
    refine ⟨⟨acc.2, j⟩, ev_elimPass_ok _ _ _ (by rw [ha0]; simp), pass_red _ _ _ (by rw [ha0]; simp), hvr.2, hjv, ?_, hlen1, ?_, ?_, ?_⟩
    · intro u v
      have := hval u v
      rw [hst] at this
      exact this
    · intro u h
      have hu := u.isLt
      have ht : tau k.val u.val = (k.succAbove u).val := by
        unfold tau
        rw [sa_val]
      rcases h with ⟨g, hg, hug⟩ | ho
      · obtain ⟨g', hg', hr⟩ := hri.2 g hg u.val hug (by omega)
        rw [ht] at hr
        exact Or.inl ⟨g', hg', hr⟩
      · change j = u.val at ho
        rcases hri.1 C.output j hst (by omega) with e | ⟨g', hg', hr⟩
        · rw [ho, ht] at e
          exact Or.inr e
        · rw [ho, ht] at hr
          exact Or.inl ⟨g', hg', hr⟩
    · intro v h
      have hv := v.isLt
      have ht : tau k.val (n + v.val) = n + 1 + v.val := by
        unfold tau
        rw [if_neg (by omega)]
        omega
      rcases h with ⟨g, hg, hvg⟩ | ho
      · obtain ⟨g', hg', hr⟩ := hri.2 g hg _ hvg (by omega)
        rw [ht] at hr
        exact Or.inl ⟨g', hg', hr⟩
      · change j = n + v.val at ho
        rcases hri.1 C.output j hst (by omega) with e | ⟨g', hg', hr⟩
        · rw [ho, ht] at e
          exact Or.inr e
        · rw [ho, ht] at hr
          exact Or.inl ⟨g', hg', hr⟩
    · by_cases h2 : 2 ≤ (C.gates.filter (fun g => decide (k.val ∈ g.inputs))).length
      · left
        have := ev_elimPass_len_two (n + m) k.val C.gates a0 hnok
          (by show k.val < (initR (n + 1 + m) k.val).length; rw [initR_len]; omega) ⟨false, hk0⟩ h2
        rw [← hacc] at this
        show acc.2.length + 2 ≤ C.gates.length
        have h0 : a0.2.length = 0 := rfl
        omega
      obtain ⟨g0, hg0mem, hkg0⟩ := hreadg
      obtain ⟨j0, hj0, hgj0⟩ := List.mem_iff_getElem.1 hg0mem
      have hg0 : gg C.gates j0 = g0 := by rw [gg_eq _ _ hj0, hgj0]
      have honly : ∀ j, j < C.gates.length → j ≠ j0 → k.val ∉ (gg C.gates j).inputs := by
        intro j hj hne hkj
        apply h2
        rw [gg_eq _ _ hj] at hkj
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · exact two_idx _ _ j j0 hlt hj0 (by simpa using hkj) (by rw [hgj0]; simpa using hkg0)
        · exact two_idx _ _ j0 j hlt hj (by rw [hgj0]; simpa using hkg0) (by simpa using hkj)
      have hNj0 : C.output = n + 1 + m + j0 → j0 + 1 = C.gates.length := by
        intro e
        rw [hsz] at hout
        omega
      -- constant case: the gate j0 gives a constant stat
      have hconst_case : (∀ mm : ℕ, ∀ S : ℕ → Bool ⊕ ℕ, S k.val = Sum.inl false →
          ∃ c, (ev_simp g0.op mm (g0.inputs.map S)).2 = Sum.inl c) → acc.2.length + 2 ≤ C.gates.length := by
        intro hcst
        set S0 := fun i => (st (n + m) C.gates a0 j0).1.getD i (Sum.inl false) with hS0
        have hS0k : S0 k.val = Sum.inl false := hkst j0 (by omega)
        obtain ⟨c, hc⟩ := hcst (n + m + (st (n + m) C.gates a0 j0).2.length) S0 hS0k
        have hstat : (st (n + m) C.gates a0 (j0 + 1)).1.getD (n + 1 + m + j0) (Sum.inl false) = Sum.inl c := by
          rw [st_succ _ _ _ j0 hj0, hgj0]
          simp only [ev_elimStep]
          rw [ev_getD_snoc_eq _ _ _ _ (by rw [hlen0 j0 (by omega)])]
          exact hc
        have hnotlast : j0 + 1 ≠ C.gates.length := by
          intro hl
          have e : C.output = n + 1 + m + j0 := by rw [hsz] at hout; omega
          have := st_stable (n + m) C.gates a0 (j0 + 1) C.gates.length (n + 1 + m + j0) (by omega) le_rfl
            (by rw [hlen0 (j0 + 1) (by omega)]; omega)
          rw [hstat, hacc_st, ← e, hst] at this
          cases this
        have hrd : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + 1 + m + j0) ≠ 0 := by
          intro h0
          exact hnotlast ((hreads j0 hj0).1 h0)
        obtain ⟨j1, hj1, hrj1⟩ := reader_of C _ hrd
        have h01 : j0 < j1 := by
          have := hRB j1 hj1 _ hrj1
          omega
        have hn0 : (ev_simp (C.gates[j0]).op (n + m + (st (n + m) C.gates a0 j0).2.length)
            ((C.gates[j0]).inputs.map fun i => (st (n + m) C.gates a0 j0).1.getD i (Sum.inl false))).1 = none := by
          rw [hgj0]
          have hn := hnok g0 hg0mem
          apply ev_simp_none_of_const
          · exact hn.1.1
          · simpa using hn.1.2
          · intro h; simpa using hn.2 h
          · exact ⟨false, List.mem_map.2 ⟨k.val, hkg0, hS0k⟩⟩
        have hn1 : (ev_simp (C.gates[j1]).op (n + m + (st (n + m) C.gates a0 j1).2.length)
            ((C.gates[j1]).inputs.map fun i => (st (n + m) C.gates a0 j1).1.getD i (Sum.inl false))).1 = none := by
          have hn := hnok _ (List.getElem_mem hj1)
          rw [← gg_eq _ _ hj1] at hn ⊢
          apply ev_simp_none_of_const
          · exact hn.1.1
          · simpa using hn.1.2
          · intro h; simpa using hn.2 h
          · refine ⟨c, List.mem_map.2 ⟨_, hrj1, ?_⟩⟩
            rw [st_stable _ _ _ (j0 + 1) j1 _ (by omega) (by omega)
              (by rw [hlen0 (j0 + 1) (by omega)]; omega)]
            exact hstat
        have := st_count (n + m) C.gates a0 j0 j1 h01 hj1 hn0 hn1
        rw [← hacc] at this
        have h0 : a0.2.length = 0 := rfl
        omega
      have hc_stat : ∀ v : Fin m, acc.1.getD (n + 1 + v.val) (Sum.inl false) = Sum.inr (n + v.val) := by
        intro v
        have hv := v.isLt
        rw [← hacc_st, st_stable _ _ _ 0 C.gates.length _ (by omega) le_rfl
          (by rw [hlen0 0 (by omega)]; omega)]
        show (initR (n + 1 + m) k.val).getD (n + 1 + v.val) (Sum.inl false) = _
        rw [initR_getD _ _ _ (by omega), if_neg (by omega), if_neg (by omega)]
        congr 1
        omega
      have hcopy : ∀ w, w ≠ k.val → (g0 = ⟨GateOp.or, [k.val, w]⟩ ∨ g0 = ⟨GateOp.or, [w, k.val]⟩) →
          ∀ v : Fin m, (((∃ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ (n + 1 + v.val) ∈ g.inputs) ∨
          (g.op = GateOp.not ∧ g.inputs.head? = some (n + 1 + v.val)))) ∨ C.output = (n + 1 + v.val)) →
          (((∃ g ∈ (⟨acc.2, j⟩ : Circuit).gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ (n + v.val) ∈ g.inputs) ∨
          (g.op = GateOp.not ∧ g.inputs.head? = some (n + v.val)))) ∨ (⟨acc.2, j⟩ : Circuit).output = (n + v.val)) := by
        intro w hw hg0eq v hv
        have hvl := v.isLt
        have hgj0' : gg C.gates j0 = ⟨GateOp.or, [k.val, w]⟩ ∨ gg C.gates j0 = ⟨GateOp.or, [w, k.val]⟩ := by
          rw [hg0]; exact hg0eq
        obtain ⟨_, F3, F4⟩ := copy_inv (n + m) (n + 1 + m) k.val C.gates (by omega) hRB hredg j0 w hj0 hw
          hgj0' honly C.gates.length le_rfl
        rw [← ha0, hacc_st] at F3 F4
        change (∀ jx, jx < C.gates.length → jx ≠ j0 → (⟨(gg C.gates jx).op, (gg C.gates jx).inputs.map
            (fun i => idx (acc.1.getD i (Sum.inl false)))⟩ : Gate) ∈ acc.2) at F3
        change j0 < C.gates.length → acc.1.getD (n + 1 + m + j0) (Sum.inl false) =
            acc.1.getD w (Sum.inl false) at F4
        have hwlt : w < n + 1 + m + j0 := by
          apply hRB j0 hj0
          rcases hgj0' with e | e <;> rw [e] <;> simp
        rcases hv with ⟨g, hg, hsense⟩ | ho
        · obtain ⟨jj, hjj, hgjj⟩ := List.mem_iff_getElem.1 hg
          have hggjj : gg C.gates jj = g := by rw [gg_eq _ _ hjj, hgjj]
          by_cases hjj0 : jj = j0
          · subst hjj0
            have hgg0 : g = g0 := by rw [← hggjj, hg0]
            rw [hgg0] at hsense
            have hwc : w = n + 1 + v.val := by
              rcases hsense with ⟨_, hc⟩ | ⟨hop, _⟩
              · rcases hg0eq with e | e <;> rw [e] at hc <;> simp at hc <;> omega
              · rcases hg0eq with e | e <;> rw [e] at hop <;> exact absurd hop (fun e => GateOp.noConfusion e)
            have hS : acc.1.getD (n + 1 + m + jj) (Sum.inl false) = Sum.inr (n + v.val) := by
              rw [F4 hjj, hwc, hc_stat]
            by_cases hlast : jj + 1 = C.gates.length
            · right
              have e : C.output = n + 1 + m + jj := by rw [hsz] at hout; omega
              rw [e, hS] at hst
              cases hst
              rfl
            · have hrd : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
                  (n + 1 + m + jj) ≠ 0 := fun h0 => hlast ((hreads jj hjj).1 h0)
              obtain ⟨j1, hj1, hrj1⟩ := reader_of C _ hrd
              have h01 : jj < j1 := by
                have := hRB j1 hj1 _ hrj1
                omega
              have hG := F3 j1 hj1 (by omega)
              have hmem : n + v.val ∈ (gg C.gates j1).inputs.map (fun i => idx (acc.1.getD i (Sum.inl false))) :=
                List.mem_map.2 ⟨_, hrj1, by rw [hS]; rfl⟩
              left
              rcases hredg j1 hj1 with ⟨hop, _⟩ | ⟨hop, hl⟩
              · exact ⟨_, hG, Or.inl ⟨hop, hmem⟩⟩
              · obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hl
                rw [hx] at hrj1 hmem
                refine ⟨_, hG, Or.inr ⟨hop, ?_⟩⟩
                simp only [List.mem_singleton] at hrj1
                show ((gg C.gates j1).inputs.map (fun i => idx (acc.1.getD i (Sum.inl false)))).head? = _
                rw [hx, ← hrj1]
                simp only [List.map_cons, List.map_nil, List.head?_cons]
                rw [hS]
                rfl
          · have hG := F3 jj hjj hjj0
            rw [hggjj] at hG
            left
            rcases hsense with ⟨hop, hc⟩ | ⟨hop, hh⟩
            · exact ⟨_, hG, Or.inl ⟨hop, List.mem_map.2 ⟨_, hc, by rw [hc_stat]; rfl⟩⟩⟩
            · refine ⟨_, hG, Or.inr ⟨hop, ?_⟩⟩
              show (g.inputs.map (fun i => idx (acc.1.getD i (Sum.inl false)))).head? = _
              rw [List.head?_map, hh]
              simp only [Option.map_some]
              rw [hc_stat]
              rfl
        · exfalso
          rw [hsz] at hout
          omega
      have hgeta : g0 = ⟨g0.op, g0.inputs⟩ := rfl
      rcases hred g0 hg0mem with ⟨hop, hl2⟩ | ⟨hop, hl1⟩
      · obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hl2
        rcases hop with hand | hor
        · left
          show acc.2.length + 2 ≤ C.gates.length
          apply hconst_case
          intro mm S hS
          rw [hand, ev_simp_and_false mm _ (by simp [hl2]) (List.mem_map.2 ⟨k.val, hkg0, hS⟩)]
          exact ⟨false, rfl⟩
        · have hkab := hkg0
          rw [hab] at hkab
          by_cases ha : a = k.val
          · by_cases hb : b = k.val
            · left
              show acc.2.length + 2 ≤ C.gates.length
              apply hconst_case
              intro mm S hS
              rw [hor, hab, ha, hb]
              simp only [List.map_cons, List.map_nil]
              rw [hS]
              exact ⟨false, rfl⟩
            · right
              exact hcopy b hb (Or.inl (by rw [hgeta, hor, hab, ha]))
          · have hb : b = k.val := by simp at hkab; omega
            right
            exact hcopy a ha (Or.inr (by rw [hgeta, hor, hab, hb]))
      · left
        show acc.2.length + 2 ≤ C.gates.length
        apply hconst_case
        intro mm S hS
        obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hl1
        have hxk : x = k.val := by rw [hx] at hkg0; simp at hkg0; omega
        rw [hop, hx, hxk]
        simp only [List.map_cons, List.map_nil]
        rw [hS]
        exact ⟨true, rfl⟩

def initK (n m K : ℕ) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin (n + (m + 1)) =>
    if i.val < K then Sum.inr i.val else if i.val = K then Sum.inl false else Sum.inr (i.val - 1)

theorem initK_len (n m K : ℕ) : (initK n m K).length = n + (m + 1) := by
  rw [initK, List.length_ofFn]

theorem initK_getD (n m K i : ℕ) (hi : i < n + (m + 1)) :
    (initK n m K).getD i (Sum.inl false) =
      if i < K then Sum.inr i else if i = K then Sum.inl false else Sum.inr (i - 1) := by
  rw [initK, ev_ofFn_getD_lt _ _ _ hi]

theorem ri_initK (n m K : ℕ) (hK : K < n + (m + 1)) : RI (n + m) K [] (initK n m K, []) := by
  refine ⟨?_, ?_⟩
  · intro i j hij hjM
    left
    by_cases hi : i < n + (m + 1)
    · rw [initK_getD n m K i hi] at hij
      split_ifs at hij with h1 h2
      · cases hij
        unfold tau
        split_ifs <;> omega
      · cases hij
        unfold tau
        split_ifs <;> omega
    · rw [List.getD_eq_default _ _ (by rw [initK_len]; omega)] at hij
      cases hij
  · intro g hg
    simp at hg

theorem inv_initK (n m : ℕ) (k : Fin (m + 1)) (u : Fin n) (v : Fin m) :
    ev_Inv (n + m) (PEqualNP.Represents.oneEach u v) (PEqualNP.Represents.oneEach u (k.succAbove v))
      (initK n m (n + k.val), []) := by
  have hk := k.isLt
  have hu := u.isLt
  have hv := v.isLt
  have hsa := sa_val k v
  refine ⟨oe_len n m u v, by rw [initK_len, oe_len], ?_⟩
  intro i
  by_cases hi : i < n + (m + 1)
  · rw [initK_getD n m _ i hi]
    split_ifs with h1 h2
    · refine ⟨by simp only [ev_statValid]; omega, ?_⟩
      show (PEqualNP.Represents.oneEach u v).getD i false = _
      rw [Bool.eq_iff_iff, oe_getD, oe_getD, hsa]
      split_ifs <;> omega
    · refine ⟨trivial, ?_⟩
      show false = _
      symm
      rw [← Bool.not_eq_true, oe_getD, hsa]
      split_ifs <;> omega
    · refine ⟨by simp only [ev_statValid]; omega, ?_⟩
      show (PEqualNP.Represents.oneEach u v).getD (i - 1) false = _
      rw [Bool.eq_iff_iff, oe_getD, oe_getD, hsa]
      split_ifs <;> omega
  · rw [List.getD_eq_default _ _ (by rw [initK_len]; omega)]
    refine ⟨trivial, ?_⟩
    show false = _
    rw [List.getD_eq_default _ _ (by rw [oe_len]; omega)]

theorem col_del : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) → PEqualNP.Represents.Represents A C → (∃ g ∈ C.gates, n + k.val ∈ g.inputs) → (∃ (u u2 : Fin n) (v v2 : Fin m), A u (k.succAbove v) ≠ A u2 (k.succAbove v2)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ (∀ g ∈ C2.gates, RedG g) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ C2.output < (n + m) + C2.gates.length ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) := by
  intro n m A k C hF hred hrep hread hnc
  have hk := k.isLt
  have hnok : ∀ g ∈ C.gates, ev_NOkGate g := by
    intro g hg
    refine ⟨hF g hg, fun hn => ?_⟩
    rcases hred g hg with ⟨hop, _⟩ | ⟨_, hl⟩
    · rcases hop with h | h
      · exact absurd (h.symm.trans hn) (fun e => GateOp.noConfusion e)
      · exact absurd (h.symm.trans hn) (fun e => GateOp.noConfusion e)
    · omega
  set acc := ev_elimPass (n + m) C.gates (initK n m (n + k.val), []) with hacc
  have hlen : acc.2.length + 1 ≤ C.gates.length := by
    have := ev_elimPass_len_lt (n + m) (n + k.val) C.gates (initK n m (n + k.val), []) hnok
      (by rw [initK_len]; omega)
      ⟨false, by rw [initK_getD n m _ _ (by omega), if_neg (by omega), if_pos rfl]⟩
      hread
    rw [← hacc] at this
    simpa using this
  have hval : ∀ (u : Fin n) (v : Fin m),
      ev_statVal (W acc.2 (PEqualNP.Represents.oneEach u v)) (acc.1.getD C.output (Sum.inl false)) =
        A u (k.succAbove v) := by
    intro u v
    have hinv := ev_Inv_pass (n + m) _ C.gates _ _ (fun g hg => hF g hg) (inv_initK n m k u v)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2]
    exact hrep u (k.succAbove v)
  have hri := ri_pass (n + m) (n + k.val) C.gates [] _ (ri_initK n m (n + k.val) (by omega))
  rw [← hacc, List.nil_append] at hri
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨u, u2, v, v2, hne⟩ := hnc
    have h1 := hval u v
    have h2 := hval u2 v2
    rw [hst] at h1 h2
    exact absurd (h1.symm.trans h2) hne
  | inr j =>
    have hvr := pass_vrb (n + m) C.gates (fun g hg => hF g hg) (initK n m (n + k.val), []) (by
      intro i
      show ev_statValid (n + m + 0) ((initK n m (n + k.val)).getD i (Sum.inl false))
      by_cases hi : i < n + (m + 1)
      · rw [initK_getD n m _ i hi]
        split_ifs <;> simp only [ev_statValid] <;> omega
      · rw [List.getD_eq_default _ _ (by rw [initK_len]; omega)]
        trivial) (RBo_nil _)
    rw [← hacc] at hvr
    have hjv : j < n + m + acc.2.length := by
      have := hvr.1 C.output
      rw [hst] at this
      exact this
    refine ⟨⟨acc.2, j⟩, ev_elimPass_ok _ _ _ (by simp), pass_red _ _ _ (by simp), hvr.2, hjv, ?_, ?_, ?_, ?_⟩
    · intro u v
      have := hval u v
      rw [hst] at this
      exact this
    · show acc.2.length + 1 ≤ C.gates.length
      exact hlen
    · intro u h
      have hu := u.isLt
      have ht : tau (n + k.val) u.val = u.val := by unfold tau; rw [if_pos (by omega)]
      rcases h with ⟨g, hg, hug⟩ | ho
      · obtain ⟨g', hg', hr⟩ := hri.2 g hg u.val hug (by omega)
        rw [ht] at hr
        exact Or.inl ⟨g', hg', hr⟩
      · change j = u.val at ho
        rcases hri.1 C.output j hst (by omega) with e | ⟨g', hg', hr⟩
        · rw [ho, ht] at e
          exact Or.inr e
        · rw [ho, ht] at hr
          exact Or.inl ⟨g', hg', hr⟩
    · intro v h
      have hv := v.isLt
      have ht : tau (n + k.val) (n + v.val) = n + (k.succAbove v).val := by
        unfold tau
        rw [sa_val]
        split_ifs <;> omega
      rcases h with ⟨g, hg, hvg⟩ | ho
      · obtain ⟨g', hg', hr⟩ := hri.2 g hg _ hvg (by omega)
        rw [ht] at hr
        exact Or.inl ⟨g', hg', hr⟩
      · change j = n + v.val at ho
        rcases hri.1 C.output j hst (by omega) with e | ⟨g', hg', hr⟩
        · rw [ho, ht] at e
          exact Or.inr e
        · rw [ho, ht] at hr
          exact Or.inl ⟨g', hg', hr⟩

def sd (n k w : ℕ) : ℕ := if w < n + k then w else w - 1

def rd (n k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sd n k)⟩

def Cd (n k : ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (rd n k), sd n k C.output⟩

theorem Cd_gateAt (n k : ℕ) (C : Circuit) (j : ℕ) : gateAt (Cd n k C) j = rd n k (gateAt C j) := by
  unfold gateAt Cd
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases C.gates[j]? <;> rfl

theorem Cd_len (n k : ℕ) (C : Circuit) : (Cd n k C).gates.length = C.gates.length := by
  simp [Cd]

theorem wires_eq {n m : ℕ} (k : Fin (m + 1)) (C : Circuit) (hC : ∀ g ∈ C.gates, n + k.val ∉ g.inputs)
    (u : Fin n) (v : Fin m) : ∀ w, w ≠ n + k.val →
    val (Cd n k.val C) (PEqualNP.Represents.oneEach u v) (sd n k.val w) =
      val C (PEqualNP.Represents.oneEach u (k.succAbove v)) w := by
  have hk := k.isLt
  have hu := u.isLt
  have hv := v.isLt
  have hsa := sa_val k v
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwk
    by_cases hw : w < n + (m + 1)
    · rw [val_input (oe_len n m u v) (by unfold sd; split_ifs <;> omega),
        val_input (oe_len n (m + 1) u (k.succAbove v)) hw, Bool.eq_iff_iff, oe_getD, oe_getD, hsa]
      unfold sd
      split_ifs <;> omega
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + (m + 1) + j := ⟨w - (n + (m + 1)), by omega⟩
      rw [show sd n k.val (n + (m + 1) + j) = n + m + j by unfold sd; split_ifs <;> omega]
      by_cases hj : j < C.gates.length
      · rw [val_gate (oe_len n m u v) (by rw [Cd_len]; exact hj),
          val_gate (oe_len n (m + 1) u (k.succAbove v)) hj, Cd_gateAt]
        unfold rd
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro w hw
        simp only [Function.comp_apply]
        have hwk2 : w ≠ n + k.val := fun e => hC _ (gateAt_mem hj) (e ▸ hw)
        by_cases hw2 : w < n + (m + 1) + j
        · rw [if_pos (by unfold sd; split_ifs <;> omega), if_pos hw2, ih w hw2 hwk2]
        · rw [if_neg (by unfold sd; split_ifs <;> omega), if_neg hw2]
      · rw [val_ge (oe_len n m u v) (by rw [Cd_len]; omega),
          val_ge (oe_len n (m + 1) u (k.succAbove v)) (by omega)]

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

theorem dropR : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + (m + 1)) C ∧ 0 < C.size ∧ C.output + 1 = (n + (m + 1)) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + (m + 1)))) → (∀ g ∈ C.gates, n + k.val ∉ g.inputs) → C.output ≠ n + k.val → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size = C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) := by
  intro n m A k C hF hrep hR hC hout
  have hk := k.isLt
  have hlen := Cd_len n k.val C
  have hsz : (Cd n k.val C).size = C.size := hlen
  refine ⟨Cd n k.val C, ?_, ?_, ?_, hsz, ?_, ?_⟩
  · intro g hg
    simp only [Cd, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact ⟨(hF g0 hg0).1, by simp only [rd, List.length_map]; exact (hF g0 hg0).2⟩
  · intro u v
    show val (Cd n k.val C) (PEqualNP.Represents.oneEach u v) (sd n k.val C.output) = _
    rw [wires_eq k C hC u v C.output hout]
    exact hrep u (k.succAbove v)
  · rcases hR with ⟨hsh, hrb, hpos, hout2, hreads⟩ | ⟨h0, hlt⟩
    · have hsz0 : C.size = C.gates.length := rfl
      left
      refine ⟨?_, ?_, by rw [hsz]; exact hpos, ?_, ?_⟩
      · intro g hg
        simp only [Cd, List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        simp only [rd, List.length_map]
        exact hsh g0 hg0
      · intro j hj i hi
        rw [Cd_len] at hj
        rw [Cd_gateAt] at hi
        simp only [rd, List.mem_map] at hi
        obtain ⟨i0, hi0, rfl⟩ := hi
        have h0 := hrb j hj i0 hi0
        have hne : i0 ≠ n + k.val := fun e => hC _ (gateAt_mem hj) (e ▸ hi0)
        unfold sd
        split_ifs <;> omega
      · show sd n k.val C.output + 1 = n + m + (Cd n k.val C).size
        rw [hsz]
        unfold sd
        split_ifs <;> omega
      · intro j hj
        rw [hsz] at hj ⊢
        rw [show n + m + j = n + (m + 1) + j - 1 by omega]
        have hr := hreads j hj
        unfold PEqualNP.MetaComplexity.NestedCover.readsIn at hr ⊢
        have e : ∑ j' ∈ Finset.range C.size, List.count (n + (m + 1) + j - 1) (gateAt (Cd n k.val C) j').inputs =
            ∑ j' ∈ Finset.range C.size, List.count (n + (m + 1) + j) (gateAt C j').inputs := by
          apply Finset.sum_congr rfl
          intro j' hj'
          rw [Finset.mem_range] at hj'
          rw [Cd_gateAt]
          simp only [rd]
          apply count_map'
          intro x hx
          have hne : x ≠ n + k.val := fun e => hC _ (gateAt_mem hj') (e ▸ hx)
          unfold sd
          split_ifs <;> omega
        rw [e]
        exact hr
    · right
      refine ⟨by rw [hsz]; exact h0, ?_⟩
      show sd n k.val C.output < n + m
      unfold sd
      split_ifs <;> omega
  · intro u h
    have hu := u.isLt
    rcases h with ⟨g, hg, hu2⟩ | ho
    · simp only [Cd, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      simp only [rd, List.mem_map] at hu2
      obtain ⟨w, hw, hwe⟩ := hu2
      have hwk : w ≠ n + k.val := fun e => hC _ hg0 (e ▸ hw)
      have e : w = u.val := by unfold sd at hwe; split_ifs at hwe <;> omega
      exact Or.inl ⟨g0, hg0, e ▸ hw⟩
    · right
      change sd n k.val C.output = u.val at ho
      unfold sd at ho
      split_ifs at ho <;> omega
  · intro v h
    have hv := v.isLt
    have hsa := sa_val k v
    rcases h with ⟨g, hg, hv2⟩ | ho
    · simp only [Cd, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      simp only [rd, List.mem_map] at hv2
      obtain ⟨w, hw, hwe⟩ := hv2
      have hwk : w ≠ n + k.val := fun e => hC _ hg0 (e ▸ hw)
      have e : w = n + (k.succAbove v).val := by
        rw [hsa]
        unfold sd at hwe
        split_ifs at hwe <;> split_ifs <;> omega
      exact Or.inl ⟨g0, hg0, e ▸ hw⟩
    · right
      change sd n k.val C.output = n + v.val at ho
      rw [hsa]
      unfold sd at ho
      split_ifs at ho <;> split_ifs <;> omega


theorem rowR : ∀ (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (k : Fin (n + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 1 + m) C ∧ 0 < C.size ∧ C.output + 1 = (n + 1 + m) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + 1 + m) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + 1 + m))) → ((∃ g ∈ C.gates, k.val ∈ g.inputs) ∨ C.output = k.val) → (∃ (u u2 : Fin n) (v v2 : Fin m), A (k.succAbove u) v ≠ A (k.succAbove u2) v2) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) v) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (k.succAbove u).val ∈ g.inputs) ∨ C.output = (k.succAbove u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + 1 + v.val) ∈ g.inputs) ∨ C.output = (n + 1 + v.val))) ∧ (C2.size + 2 ≤ C.size ∨ ∀ v : Fin m, ((∃ g ∈ C.gates, (n + 1 + v.val) ∈ g.inputs) ∨ C.output = (n + 1 + v.val)) → ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val))) := by
  intro n m A k C hF hrep hR hread hnc
  have hk := k.isLt
  rcases hR with ⟨hred, hrb, hpos, hout, hreads⟩ | ⟨h0, hlt⟩
  · obtain ⟨C1, hF1, hsh1, hrb1, hov1, hrep1, hsz1, hrow1, hcol1, hdisj1⟩ :=
      row_del n m A k C hF hrep hred hrb hpos hout hreads hread hnc
    obtain ⟨E, hev, hRd, hszE, hrdE, hpres⟩ := clean (n + m) C1 hsh1 hrb1 hov1
    refine ⟨E, ?_, ?_, hRd, ?_, ?_, ?_, ?_⟩
    · intro g hg
      have hRd' := hRd
      unfold Rdc at hRd'
      rcases hRd' with ⟨hshE, -⟩ | ⟨h0, -⟩
      · rcases hshE g hg with ⟨hop, hl⟩ | ⟨hop, hl⟩
        · exact ⟨by rcases hop with h | h <;> rw [h] <;> simp, by omega⟩
        · exact ⟨by rw [hop]; simp, by omega⟩
      · have h0' : E.gates.length = 0 := h0
        rw [List.length_eq_zero_iff] at h0'
        rw [h0'] at hg
        simp at hg
    · intro u v
      rw [hev _ (oe_len n m u v)]
      exact hrep1 u v
    · omega
    · intro u h
      exact hrow1 u (hrdE u.val (by have := u.isLt; omega) h)
    · intro v h
      exact hcol1 v (hrdE (n + v.val) (by have := v.isLt; omega) h)
    · rcases hdisj1 with h2 | hall
      · left
        omega
      · by_cases hE : E.size = C1.size
        · right
          intro v hv
          exact hpres hE (n + v.val) (by have := v.isLt; omega)
            (sense_mem _ _ _ (hall v (mem_sense _ _ _ hred hv)))
        · left
          omega
  · exfalso
    have h0' : C.gates.length = 0 := h0
    have hgates : C.gates = [] := List.length_eq_zero_iff.1 h0'
    rcases hread with ⟨g, hg, _⟩ | ho
    · rw [hgates] at hg
      simp at hg
    · obtain ⟨u, u2, v, v2, hne⟩ := hnc
      apply hne
      have hz : ∀ (u : Fin n) (v : Fin m), A (k.succAbove u) v = false := by
        intro u v
        have hu := u.isLt
        have hv := v.isLt
        have hsa := sa_val k u
        rw [← hrep (k.succAbove u) v]
        show (W C.gates _).getD C.output false = false
        rw [W_prefix _ _ _ (by rw [oe_len]; omega), ho, ← Bool.not_eq_true, oe_getD, hsa]
        split_ifs <;> omega
      rw [hz, hz]

theorem colR : ∀ (n m : ℕ) (A : Fin n → Fin (m + 1) → Bool) (k : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + (m + 1)) C ∧ 0 < C.size ∧ C.output + 1 = (n + (m + 1)) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + (m + 1)))) → (∃ g ∈ C.gates, n + k.val ∈ g.inputs) → (∃ (u u2 : Fin n) (v v2 : Fin m), A u (k.succAbove v) ≠ A u2 (k.succAbove v2)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A u (k.succAbove v)) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, u.val ∈ g.inputs) ∨ C.output = u.val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + (k.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + (k.succAbove v).val))) := by
  intro n m A k C hF hrep hR hread hnc
  have hk := k.isLt
  have hred : ∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1) := by
    rcases hR with ⟨h, -⟩ | ⟨h0, -⟩
    · exact h
    · exfalso
      obtain ⟨g, hg, -⟩ := hread
      have h0' : C.gates.length = 0 := h0
      rw [List.length_eq_zero_iff] at h0'
      rw [h0'] at hg
      simp at hg
  obtain ⟨C1, hF1, hsh1, hrb1, hov1, hrep1, hsz1, hrow1, hcol1⟩ := col_del n m A k C hF hred hrep hread hnc
  obtain ⟨E, hev, hRd, hszE, hrdE, -⟩ := clean (n + m) C1 hsh1 hrb1 hov1
  refine ⟨E, ?_, ?_, hRd, ?_, ?_, ?_⟩
  · intro g hg
    have hRd' := hRd
    unfold Rdc at hRd'
    rcases hRd' with ⟨hshE, -⟩ | ⟨h0, -⟩
    · rcases hshE g hg with ⟨hop, hl⟩ | ⟨hop, hl⟩
      · exact ⟨by rcases hop with h | h <;> rw [h] <;> simp, by omega⟩
      · exact ⟨by rw [hop]; simp, by omega⟩
    · have h0' : E.gates.length = 0 := h0
      rw [List.length_eq_zero_iff] at h0'
      rw [h0'] at hg
      simp at hg
  · intro u v
    rw [hev _ (oe_len n m u v)]
    exact hrep1 u v
  · omega
  · intro u h
    exact hrow1 u (hrdE u.val (by have := u.isLt; omega) h)
  · intro v h
    exact hcol1 v (hrdE (n + v.val) (by have := v.isLt; omega) h)

theorem main_aux : ∀ (n m : ℕ) (A : Fin (n + 1) → Fin (m + 1) → Bool) (k : Fin (n + 1)) (l : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 1 + (m + 1)) C ∧ 0 < C.size ∧ C.output + 1 = (n + 1 + (m + 1)) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + 1 + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + 1 + (m + 1)))) → ((∃ g ∈ C.gates, k.val ∈ g.inputs) ∨ C.output = k.val) → ((∃ g ∈ C.gates, (n + 1 + l.val) ∈ g.inputs) ∨ C.output = (n + 1 + l.val)) → (∃ (u u2 : Fin n) (v v2 : Fin (m + 1)), A (k.succAbove u) v ≠ A (k.succAbove u2) v2) → (∃ (u u2 : Fin n) (v v2 : Fin m), A (k.succAbove u) (l.succAbove v) ≠ A (k.succAbove u2) (l.succAbove v2)) → ¬ (∀ (u : Fin n) (v : Fin (m + 1)), A (k.succAbove u) v = decide (v = l)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) (l.succAbove v)) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size + 2 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (k.succAbove u).val ∈ g.inputs) ∨ C.output = (k.succAbove u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + 1 + (l.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + 1 + (l.succAbove v).val))) := by
  intro n m A k l C hF hrep hR hreadk hreadl hnc1 hnc2 hnind
  have hl := l.isLt
  obtain ⟨C1, hF1, hrep1, hRd1, hsz1, hrow1, hcol1, hdisj1⟩ := rowR n (m + 1) A k C hF hrep hR hreadk hnc1
  by_cases hcl : ∃ g ∈ C1.gates, n + l.val ∈ g.inputs
  · obtain ⟨C2, hF2, hrep2, hRd2, hsz2, hrow2, hcol2⟩ :=
      colR n m (fun u v => A (k.succAbove u) v) l C1 hF1 hrep1 hRd1 hcl hnc2
    refine ⟨C2, hF2, hrep2, hRd2, by omega, ?_, ?_⟩
    · intro u h
      exact hrow1 u (hrow2 u h)
    · intro v h
      exact hcol1 (l.succAbove v) (hcol2 v h)
  · have hno : ∀ g ∈ C1.gates, n + l.val ∉ g.inputs := fun g hg h => hcl ⟨g, hg, h⟩
    have hout1 : C1.output ≠ n + l.val := by
      intro e
      apply hnind
      intro u v
      have hu := u.isLt
      have hv := v.isLt
      have h1 : C1.eval (PEqualNP.Represents.oneEach u v) = A (k.succAbove u) v := hrep1 u v
      rw [← h1]
      show (C1.wires (PEqualNP.Represents.oneEach u v)).getD C1.output false = _
      rw [e, show (C1.wires (PEqualNP.Represents.oneEach u v)).getD (n + l.val) false =
        (PEqualNP.Represents.oneEach u v).getD (n + l.val) false from
          W_prefix _ _ _ (by rw [oe_len]; omega)]
      rw [Bool.eq_iff_iff, oe_getD]
      simp only [decide_eq_true_eq, Fin.ext_iff]
      omega
    obtain ⟨C2, hF2, hrep2, hRd2, hsz2, hrow2, hcol2⟩ :=
      dropR n m (fun u v => A (k.succAbove u) v) l C1 hF1 hrep1 hRd1 hno hout1
    have hsz2' : C2.size + 2 ≤ C.size := by
      rcases hdisj1 with h2 | hall
      · omega
      · exfalso
        rcases hall l hreadl with ⟨g, hg, hw⟩ | ho
        · exact hno g hg hw
        · exact hout1 ho
    refine ⟨C2, hF2, hrep2, hRd2, hsz2', ?_, ?_⟩
    · intro u h
      exact hrow1 u (hrow2 u h)
    · intro v h
      exact hcol1 (l.succAbove v) (hcol2 v h)

end PEqualNP.Outside.L_meta_24698

theorem PEqualNP.Outside.L_meta_24698 : ∀ (n m : ℕ) (A : Fin (n + 1) → Fin (m + 1) → Bool) (k : Fin (n + 1)) (l : Fin (m + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 1 + (m + 1)) C ∧ 0 < C.size ∧ C.output + 1 = (n + 1 + (m + 1)) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + 1 + (m + 1)) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + 1 + (m + 1)))) → ((∃ g ∈ C.gates, k.val ∈ g.inputs) ∨ C.output = k.val) → ((∃ g ∈ C.gates, (n + 1 + l.val) ∈ g.inputs) ∨ C.output = (n + 1 + l.val)) → (∃ (u u2 : Fin n) (v v2 : Fin (m + 1)), A (k.succAbove u) v ≠ A (k.succAbove u2) v2) → (∃ (u u2 : Fin n) (v v2 : Fin m), A (k.succAbove u) (l.succAbove v) ≠ A (k.succAbove u2) (l.succAbove v2)) → ¬ (∀ (u : Fin n) (v : Fin (m + 1)), A (k.succAbove u) v = decide (v = l)) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) (l.succAbove v)) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size + 2 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (k.succAbove u).val ∈ g.inputs) ∨ C.output = (k.succAbove u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + 1 + (l.succAbove v).val) ∈ g.inputs) ∨ C.output = (n + 1 + (l.succAbove v).val))) :=
  PEqualNP.Outside.L_meta_24698.main_aux
