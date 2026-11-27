import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25540_aux

namespace Crossed

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

theorem uniq (C : Circuit) (w j0 j : ℕ) (hj0 : j0 < C.gates.length) (hj : j < C.gates.length)
    (h1 : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w = 1)
    (hw0 : w ∈ (gateAt C j0).inputs) (hw : w ∈ (gateAt C j).inputs) : j = j0 := by
  by_contra hne
  unfold PEqualNP.MetaComplexity.NestedCover.readsIn at h1
  have hs := Finset.add_le_sum (f := fun k => (gateAt C k).inputs.count w) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 (show j0 < C.size from hj0)) (Finset.mem_range.2 (show j < C.size from hj)) (Ne.symm hne)
  have c0 := List.count_pos_iff.2 hw0
  have c1 := List.count_pos_iff.2 hw
  omega

theorem main_aux : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
  (C : PEqualNP.CircuitLowerBounds.Circuit)
  (u u' : Fin n) (b b' : Fin m),
  let x := u.val
  let x' := u'.val
  let y := n + b.val
  let y' := n + b'.val
  let paired := fun (r c : ℕ) =>
    ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (g.inputs = [r, c] ∨ g.inputs = [c, r])
  u ≠ u' → b ≠ b' →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  paired x y → paired x' y' →
  (∀ w ∈ [x, x', y, y'],
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w = 1) →
  C.output ∉ [x, x', y, y'] →
  G u b' = G u' b := by
  intro n m G C u u' b b'
  dsimp only
  intro huu hbb hrb hrep hp1 hp2 hreads hout
  have hu := u.isLt
  have hu' := u'.isLt
  have hb := b.isLt
  have hb' := b'.isLt
  have huu' : u.val ≠ u'.val := fun e => huu (Fin.ext e)
  have hbb' : b.val ≠ b'.val := fun e => hbb (Fin.ext e)
  obtain ⟨g0, hg0, hop0, hin0⟩ := hp1
  obtain ⟨g1, hg1, hop1, hin1⟩ := hp2
  obtain ⟨j0, hj0, hgj0⟩ := List.mem_iff_getElem.1 hg0
  obtain ⟨j1, hj1, hgj1⟩ := List.mem_iff_getElem.1 hg1
  have ha0 : gateAt C j0 = g0 := by rw [gateAt_eq hj0, hgj0]
  have ha1 : gateAt C j1 = g1 := by rw [gateAt_eq hj1, hgj1]
  have hr := fun w hw => hreads w hw
  have rx := hr u.val (by simp)
  have rx' := hr u'.val (by simp)
  have ry := hr (n + b.val) (by simp)
  have ry' := hr (n + b'.val) (by simp)
  have m0x : u.val ∈ (gateAt C j0).inputs := by rw [ha0]; rcases hin0 with h | h <;> rw [h] <;> simp
  have m0y : n + b.val ∈ (gateAt C j0).inputs := by rw [ha0]; rcases hin0 with h | h <;> rw [h] <;> simp
  have m1x : u'.val ∈ (gateAt C j1).inputs := by rw [ha1]; rcases hin1 with h | h <;> rw [h] <;> simp
  have m1y : n + b'.val ∈ (gateAt C j1).inputs := by rw [ha1]; rcases hin1 with h | h <;> rw [h] <;> simp
  set P := PEqualNP.Represents.oneEach u b' with hP
  set Q := PEqualNP.Represents.oneEach u' b with hQ
  have hPl : P.length = n + m := oe_len n m u b'
  have hQl : Q.length = n + m := oe_len n m u' b
  have vP : ∀ i, i < n + m → (val C P i = true ↔ (i = u.val ∨ i = n + b'.val)) := by
    intro i hi
    rw [val_input hPl hi, hP, oe_getD]
  have vQ : ∀ i, i < n + m → (val C Q i = true ↔ (i = u'.val ∨ i = n + b.val)) := by
    intro i hi
    rw [val_input hQl hi, hQ, oe_getD]
  have key : ∀ w, w ≠ u.val → w ≠ u'.val → w ≠ n + b.val → w ≠ n + b'.val → val C P w = val C Q w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h1 h2 h3 h4
      by_cases hw : w < n + m
      · rw [Bool.eq_iff_iff, vP w hw, vQ w hw]
        omega
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + m + j := ⟨w - (n + m), by omega⟩
        by_cases hj : j < C.gates.length
        · rw [val_gate_rb hPl hj (hrb j hj), val_gate_rb hQl hj (hrb j hj)]
          by_cases e0 : j = j0
          · subst e0
            have t1 : val C P u.val = true := (vP _ (by omega)).2 (Or.inl rfl)
            have t2 : val C Q (n + b.val) = true := (vQ _ (by omega)).2 (Or.inr rfl)
            rw [ha0, hop0]
            rcases hin0 with h | h <;> rw [h] <;> simp only [List.map_cons, List.map_nil, eval_or2] <;>
              rw [t1, t2] <;> simp
          · by_cases e1 : j = j1
            · subst e1
              have t1 : val C P (n + b'.val) = true := (vP _ (by omega)).2 (Or.inr rfl)
              have t2 : val C Q u'.val = true := (vQ _ (by omega)).2 (Or.inl rfl)
              rw [ha1, hop1]
              rcases hin1 with h | h <;> rw [h] <;> simp only [List.map_cons, List.map_nil, eval_or2] <;>
                rw [t1, t2] <;> simp
            · congr 1
              apply List.map_congr_left
              intro i hi
              have hlt := hrb j hj i hi
              apply ih i (by omega)
              · intro e; rw [e] at hi; exact e0 (uniq C _ j0 j hj0 hj rx m0x hi)
              · intro e; rw [e] at hi; exact e1 (uniq C _ j1 j hj1 hj rx' m1x hi)
              · intro e; rw [e] at hi; exact e0 (uniq C _ j0 j hj0 hj ry m0y hi)
              · intro e; rw [e] at hi; exact e1 (uniq C _ j1 j hj1 hj ry' m1y hi)
        · rw [val_ge hPl (by omega), val_ge hQl (by omega)]
  have ho := key C.output (fun e => hout (by rw [e]; simp)) (fun e => hout (by rw [e]; simp))
    (fun e => hout (by rw [e]; simp)) (fun e => hout (by rw [e]; simp))
  have e1 : C.eval P = G u b' := hrep u b'
  have e2 : C.eval Q = G u' b := hrep u' b
  rw [← e1, ← e2]
  exact ho

end Crossed

namespace Tags

def sigs {n : ℕ} (rows cols : Finset (Fin n)) (u v : Fin n) : Finset (Fin 3 × Fin n) :=
  (Finset.univ : Finset (Fin 3 × Fin n)).filter (fun s =>
      if s.1 = 0 then s.2 = u ∨ s.2 = v
      else if s.1 = 1 then s.2 ∈ rows ∧ s.2 = u
      else s.2 ∈ cols ∧ s.2 = v)

lemma mem0 {n : ℕ} (rows cols : Finset (Fin n)) (a u v : Fin n) :
    ((0 : Fin 3), a) ∈ sigs rows cols u v ↔ (a = u ∨ a = v) := by
  simp [sigs]

lemma mem1 {n : ℕ} (rows cols : Finset (Fin n)) (a u v : Fin n) :
    ((1 : Fin 3), a) ∈ sigs rows cols u v ↔ (a ∈ rows ∧ a = u) := by
  simp [sigs]

lemma mem2 {n : ℕ} (rows cols : Finset (Fin n)) (a u v : Fin n) :
    ((2 : Fin 3), a) ∈ sigs rows cols u v ↔ (a ∈ cols ∧ a = v) := by
  simp [sigs]

lemma sigs_swap {n : ℕ} (rows cols : Finset (Fin n)) (i j : Fin n)
    (hi : i ∉ rows) (hj : j ∉ cols) (hj' : j ∉ rows) (hi' : i ∉ cols) :
    sigs rows cols i j = sigs rows cols j i := by
  have hk : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  ext ⟨k, a⟩
  rcases hk k with rfl | rfl | rfl
  · rw [mem0, mem0]
    exact or_comm
  · rw [mem1, mem1]
    constructor
    · rintro ⟨h, rfl⟩
      exact absurd h hi
    · rintro ⟨h, rfl⟩
      exact absurd h hj'
  · rw [mem2, mem2]
    constructor
    · rintro ⟨h, rfl⟩
      exact absurd h hj
    · rintro ⟨h, rfl⟩
      exact absurd h hi'

def tm {n : ℕ} (rows cols : Finset (Fin n)) (a b : Fin n) :
    (Fin 3 × Fin n) × (Fin 3 × Fin n) :=
  if a ∈ rows then ((1, a), (0, b))
  else if b ∈ cols then ((0, a), (2, b))
  else ((0, a), (0, b))

def tag {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (a b : Fin n) : ℕ :=
  if G a b = true then
    (if a ≠ b ∧ (a ∈ rows ∨ b ∈ cols ∨ G b a = true) then 0 else 1)
  else (if a = b then 3 else 2)

def isOn {n : ℕ} (rows cols : Finset (Fin n)) (a b u v : Fin n) : Prop :=
  (tm rows cols a b).1 ∈ sigs rows cols u v ∧ (tm rows cols a b).2 ∈ sigs rows cols u v

lemma isOn_self {n : ℕ} (rows cols : Finset (Fin n)) (u v : Fin n) :
    isOn rows cols u v u v := by
  unfold isOn tm
  split_ifs with h1 h2
  · exact ⟨(mem1 rows cols u u v).mpr ⟨h1, rfl⟩, (mem0 rows cols v u v).mpr (Or.inr rfl)⟩
  · exact ⟨(mem0 rows cols u u v).mpr (Or.inl rfl), (mem2 rows cols v u v).mpr ⟨h2, rfl⟩⟩
  · exact ⟨(mem0 rows cols u u v).mpr (Or.inl rfl), (mem0 rows cols v u v).mpr (Or.inr rfl)⟩

lemma isOn_gen {n : ℕ} (rows cols : Finset (Fin n)) (a b u v : Fin n)
    (h : isOn rows cols a b u v) : (a = u ∨ a = v) ∧ (b = u ∨ b = v) := by
  unfold isOn tm at h
  split_ifs at h with h1 h2
  · obtain ⟨h3, h4⟩ := h
    have h3' := (mem1 rows cols a u v).mp h3
    have h4' := (mem0 rows cols b u v).mp h4
    exact ⟨Or.inl h3'.2, h4'⟩
  · obtain ⟨h3, h4⟩ := h
    have h3' := (mem0 rows cols a u v).mp h3
    have h4' := (mem2 rows cols b u v).mp h4
    exact ⟨h3', Or.inr h4'.2⟩
  · obtain ⟨h3, h4⟩ := h
    exact ⟨(mem0 rows cols a u v).mp h3, (mem0 rows cols b u v).mp h4⟩

lemma isOn_X {n : ℕ} (rows cols : Finset (Fin n)) (a b u v : Fin n)
    (h : isOn rows cols a b u v) (hab : a ≠ b) (hX : a ∈ rows ∨ b ∈ cols) :
    a = u ∧ b = v := by
  unfold isOn tm at h
  split_ifs at h with h1 h2
  · obtain ⟨h3, h4⟩ := h
    have h3' := (mem1 rows cols a u v).mp h3
    have h4' := (mem0 rows cols b u v).mp h4
    rcases h4' with h5 | h5
    · exact absurd (h3'.2.trans h5.symm) hab
    · exact ⟨h3'.2, h5⟩
  · obtain ⟨h3, h4⟩ := h
    have h3' := (mem0 rows cols a u v).mp h3
    have h4' := (mem2 rows cols b u v).mp h4
    rcases h3' with h5 | h5
    · exact ⟨h5, h4'.2⟩
    · exact absurd (h5.trans h4'.2.symm) hab
  · rcases hX with hX | hX
    · exact absurd hX h1
    · exact absurd hX h2

lemma tag0 {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (a b : Fin n)
    (h : tag G rows cols a b = 0) :
    G a b = true ∧ a ≠ b ∧ (a ∈ rows ∨ b ∈ cols ∨ G b a = true) := by
  unfold tag at h
  split_ifs at h with h1 h2 h3
  exact ⟨h1, h2⟩

lemma tag1 {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (a b : Fin n)
    (h : tag G rows cols a b = 1) :
    G a b = true ∧ ¬ (a ≠ b ∧ (a ∈ rows ∨ b ∈ cols ∨ G b a = true)) := by
  unfold tag at h
  split_ifs at h with h1 h2 h3
  all_goals first | exact ⟨h1, h2⟩ | omega

lemma tag2 {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (a b : Fin n)
    (h : tag G rows cols a b = 2) :
    G a b = false ∧ a ≠ b := by
  unfold tag at h
  split_ifs at h with h1 h2 h3
  all_goals first | omega | exact ⟨by simpa using h1, by assumption⟩

lemma tag2' {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (a b : Fin n)
    (hG : G a b = false) (hab : a ≠ b) : tag G rows cols a b = 2 := by
  unfold tag
  split_ifs with h1 h2
  all_goals first | rfl | exact absurd h1 (by simp [hG])

lemma tag01 {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n)) (a b : Fin n)
    (hG : G a b = true) : tag G rows cols a b = 0 ∨ tag G rows cols a b = 1 := by
  unfold tag
  split_ifs with h1
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

lemma correct {n : ℕ} (G : Fin n → Fin n → Bool) (rows cols : Finset (Fin n))
    (hcov : ∀ i j, G i j = true → G j i = false → i ∈ rows ∨ j ∈ cols ∨ j ∈ rows ∨ i ∈ cols)
    (u v : Fin n) :
    G u v = true ↔ ((∃ a b, tag G rows cols a b = 0 ∧ isOn rows cols a b u v) ∨
      ((∃ a b, tag G rows cols a b = 1 ∧ isOn rows cols a b u v) ∧
        ¬ ∃ a b, tag G rows cols a b = 2 ∧ isOn rows cols a b u v)) := by
  constructor
  · intro hG
    rcases tag01 G rows cols u v hG with h0 | h1
    · exact Or.inl ⟨u, v, h0, isOn_self rows cols u v⟩
    · refine Or.inr ⟨⟨u, v, h1, isOn_self rows cols u v⟩, ?_⟩
      rintro ⟨a, b, h2, hon⟩
      obtain ⟨hGab, hab⟩ := tag2 G rows cols a b h2
      obtain ⟨-, hn⟩ := tag1 G rows cols u v h1
      obtain ⟨ha, hb⟩ := isOn_gen rows cols a b u v hon
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hab (ha.trans hb.symm)
      · rw [ha, hb, hG] at hGab
        exact absurd hGab (by simp)
      · rw [ha, hb] at hGab hab hon
        have hc := hcov u v hG hGab
        have hX : v ∈ rows ∨ u ∈ cols := by
          rcases hc with h | h | h | h
          · exact absurd ⟨Ne.symm hab, Or.inl h⟩ hn
          · exact absurd ⟨Ne.symm hab, Or.inr (Or.inl h)⟩ hn
          · exact Or.inl h
          · exact Or.inr h
        have h3 := isOn_X rows cols v u u v hon hab hX
        exact hab h3.1
      · exact hab (ha.trans hb.symm)
  · rintro (⟨a, b, h0, hon⟩ | ⟨⟨a, b, h1, hon⟩, hH⟩)
    · obtain ⟨hGab, hab, hX⟩ := tag0 G rows cols a b h0
      obtain ⟨ha, hb⟩ := isOn_gen rows cols a b u v hon
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · rw [ha, hb] at hGab
        exact hGab
      · rcases hX with hX | hX | hX
        · have h := isOn_X rows cols a b u v hon hab (Or.inl hX)
          rw [h.1, h.2] at hGab
          exact hGab
        · have h := isOn_X rows cols a b u v hon hab (Or.inr hX)
          rw [h.1, h.2] at hGab
          exact hGab
        · rw [ha, hb] at hX
          exact hX
      · exact absurd (ha.trans hb.symm) hab
    · by_contra hG
      have hG' : G u v = false := by simpa using hG
      by_cases huv : u = v
      · obtain ⟨hGab, -⟩ := tag1 G rows cols a b h1
        obtain ⟨ha, hb⟩ := isOn_gen rows cols a b u v hon
        have ha' : a = u := by
          rcases ha with h | h
          · exact h
          · exact h.trans huv.symm
        have hb' : b = v := by
          rcases hb with h | h
          · exact h.trans huv
          · exact h
        rw [ha', hb'] at hGab
        exact hG hGab
      · exact hH ⟨u, v, tag2' G rows cols u v hG' huv, isOn_self rows cols u v⟩

end Tags

namespace Absent

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

variable {n : ℕ}

abbrev Pred (n : ℕ) := Fin n → Fin n → Prop
def lit (i : Fin n) : Pred n := fun u v => i = u ∨ i = v
def input (u v : Fin n) := List.ofFn fun i : Fin n => decide (i = u ∨ i = v)

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def vals (gs : List Gate) (u v : Fin n) := gs.foldl step (input u v)

lemma foldLen (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma vals_snoc (gs : List Gate) (g : Gate) (u v : Fin n) :
    vals (gs ++ [g]) u v = step (vals gs u v) g := by simp [vals, List.foldl_append]

lemma valLen (gs : List Gate) (u v : Fin n) : (vals gs u v).length = n + gs.length := by
  simp [vals, foldLen, input]

structure Net (n : ℕ) where
  gs : List Gate
  mono : Monotone2 ⟨gs, 0⟩
  back : ReadsBack n ⟨gs, 0⟩

def Has (N : Net n) (p : Pred n) : Prop :=
  ∃ i, i < n + N.gs.length ∧ ∀ u v, (vals N.gs u v).getD i false = true ↔ p u v

lemma Has.congr {N : Net n} {p q : Pred n} (h : Has N p) (e : ∀ u v, p u v ↔ q u v) :
    Has N q := by
  obtain ⟨i, hi, he⟩ := h
  exact ⟨i, hi, fun u v => (he u v).trans (e u v)⟩

def Ext (A B : Net n) (k : ℕ) : Prop :=
  B.gs.length ≤ A.gs.length + k ∧ ∀ p, Has A p → Has B p

lemma Ext.refl (A : Net n) : Ext A A 0 := ⟨by omega, fun _ h => h⟩
lemma Ext.trans {A B C : Net n} {a b : ℕ} (h : Ext A B a) (h' : Ext B C b) :
    Ext A C (a+b) := ⟨by have := h.1; have := h'.1; omega, fun p x => h'.2 p (h.2 p x)⟩
lemma Ext.weaken {A B : Net n} {a b : ℕ} (h : Ext A B a) (le : a ≤ b) :
    Ext A B b := ⟨by have := h.1; omega, h.2⟩

lemma getLeft {α : Type} (a b : List α) (i : ℕ) (d : α) (hi : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]

lemma getLast {α : Type} (a : List α) (x d : α) : (a ++ [x]).getD a.length d = x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append]

def snoc (A : Net n) (g : Gate) (hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hb : ∀ i ∈ g.inputs, i < n + A.gs.length) : Net n where
  gs := A.gs ++ [g]
  mono := by
    intro x hx
    change x ∈ A.gs ++ [g] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact A.mono x hx
    · obtain rfl := List.mem_singleton.mp hx
      exact hm
  back := by
    intro j hj i hi
    change j < (A.gs ++ [g]).length at hj
    change i ∈ ((A.gs ++ [g]).getD j _).inputs at hi
    by_cases h : j < A.gs.length
    · rw [getLeft _ _ _ _ h] at hi
      exact A.back j h i hi
    · have hj' : j = A.gs.length := by simp at hj; omega
      subst j
      rw [getLast] at hi
      exact hb i hi

lemma snocExt (A : Net n) (g : Gate) (hm hb) : Ext A (snoc A g hm hb) 1 := by
  constructor
  · simp [snoc]
  · rintro p ⟨i, hi, he⟩
    refine ⟨i, by simp [snoc]; omega, fun u v => ?_⟩
    change (vals (A.gs ++ [g]) u v).getD i false = true ↔ p u v
    rw [vals_snoc, step, getLeft _ _ _ _ (by simpa [valLen] using hi)]
    exact he u v

lemma newHas (A : Net n) (g : Gate) (hm hb) :
    Has (snoc A g hm hb) (fun u v => g.op.eval (g.inputs.map fun i => (vals A.gs u v).getD i false) = true) := by
  refine ⟨n + A.gs.length, by simp [snoc], fun u v => ?_⟩
  change (vals (A.gs ++ [g]) u v).getD _ false = true ↔ _
  rw [vals_snoc, ← valLen A.gs u v, step, getLast]

lemma combine (A : Net n) {p q : Pred n} (hp : Has A p) (hq : Has A q) (both : Bool) :
    ∃ B, Ext A B 1 ∧ Has B (fun u v => if both then p u v ∧ q u v else p u v ∨ q u v) := by
  obtain ⟨i, hi, ei⟩ := hp
  obtain ⟨j, hj, ej⟩ := hq
  let g : Gate := ⟨if both then GateOp.and else GateOp.or, [i,j]⟩
  have hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by cases both <;> simp [g]
  have hb : ∀ a ∈ g.inputs, a < n + A.gs.length := by simp [g, hi, hj]
  refine ⟨_, snocExt A g hm hb, (newHas A g hm hb).congr ?_⟩
  intro u v
  cases both <;> simp [g, GateOp.eval, ← ei u v, ← ej u v]

def blank (n : ℕ) : Net n where
  gs := []
  mono := by intro g h; cases h
  back := by intro j h; exact (Nat.not_lt_zero j h).elim

lemma raw (i : Fin n) : Has (blank n) (lit i) := by
  refine ⟨i.val, by simpa [blank] using i.isLt, fun u v => ?_⟩
  simp [blank, vals, input, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, lit]

lemma seed (n : ℕ) : ∃ A : Net n, A.gs.length ≤ 1 ∧ Has A (fun _ _ => False) ∧ ∀ i, Has A (lit i) := by
  let g : Gate := ⟨.or, []⟩
  have hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by simp [g]
  have hb : ∀ i ∈ g.inputs, i < n + (blank n).gs.length := by simp [g]
  have e := snocExt (blank n) g hm hb
  exact ⟨_, by simpa [blank] using e.1, (newHas (blank n) g hm hb).congr (by simp [g, GateOp.eval]), fun i => e.2 _ (raw i)⟩

def group (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) (a : Fin n) : Pred n :=
  fun u v => (u ∈ s ∧ f u = some a) ∨ (v ∈ s ∧ f v = some a)

lemma packGroups (A : Net n) (hz : Has A (fun _ _ => False)) (hr : ∀ i, Has A (lit i))
    (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) :
    ∃ B, Ext A B s.card ∧ ∀ a, Has B (group f s a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨A, by simpa using Ext.refl A, fun a => hz.congr (by simp [group])⟩
  | @insert i s hi ih =>
    obtain ⟨B, e, h⟩ := ih
    cases hf : f i with
    | none =>
      refine ⟨B, e.weaken (by simp [hi]), fun a => (h a).congr ?_⟩
      intro u v
      simp only [group, Finset.mem_insert]
      grind
    | some a =>
      obtain ⟨C, e', hw⟩ := combine B (h a) (e.2 _ (hr i)) false
      refine ⟨C, by simpa [hi] using e.trans e', fun b => ?_⟩
      by_cases hab : a = b
      · subst b
        apply hw.congr
        intro u v
        simp only [group, lit, Bool.false_eq_true, if_false, Finset.mem_insert]
        grind
      · apply (e'.2 _ (h b)).congr
        intro u v
        simp only [group, Finset.mem_insert]
        grind

def seen (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) (i : Fin n) :=
  ∃ a ∈ s, f i = some a
def anySeen (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) : Pred n :=
  fun u v => seen f s u ∨ seen f s v
def twoSeen (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) : Pred n :=
  fun u v => seen f s u ∧ seen f s v ∧ f u ≠ f v

lemma seen_insert (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) (a i : Fin n) :
    seen f (insert a s) i ↔ f i = some a ∨ seen f s i := by
  simp [seen, Finset.exists_mem_insert]

lemma two_insert (f : Fin n → Option (Fin n)) (s : Finset (Fin n)) (a : Fin n) (ha : a ∉ s) (u v : Fin n) :
    (twoSeen f s u v ∨ ((f u = some a ∨ f v = some a) ∧ anySeen f s u v)) ↔
      twoSeen f (insert a s) u v := by
  have hdis (i : Fin n) : f i = some a → ¬seen f s i := by
    rintro he ⟨b, hb, hb'⟩
    grind
  have hsame : f u = f v → (seen f s u ↔ seen f s v) := by intro h; simp [seen, h]
  simp only [twoSeen, anySeen, seen_insert]
  have := hdis u
  have := hdis v
  grind

lemma scan (A : Net n) (hz : Has A (fun _ _ => False)) (f : Fin n → Option (Fin n))
    (hgrp : ∀ a, Has A (fun u v => f u = some a ∨ f v = some a)) (s : Finset (Fin n)) :
    ∃ B, Ext A B (3*s.card) ∧ Has B (anySeen f s) ∧ Has B (twoSeen f s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨A, by simpa using Ext.refl A, hz.congr (by simp [seen,anySeen]), hz.congr (by simp [seen,twoSeen])⟩
  | @insert a s ha ih =>
    obtain ⟨B,e,oldAny,oldTwo⟩ := ih
    have tag := e.2 _ (hgrp a)
    obtain ⟨C,eC,hCross⟩ := combine B tag oldAny true
    obtain ⟨D,eD,hTwo⟩ := combine C (eC.2 _ oldTwo) hCross false
    obtain ⟨E,eE,hAny⟩ := combine D (eD.2 _ (eC.2 _ tag)) (eD.2 _ (eC.2 _ oldAny)) false
    refine ⟨E, (((e.trans eC).trans eD).trans eE).weaken (by rw [Finset.card_insert_of_notMem ha]; omega),
      hAny.congr ?_, (eE.2 _ hTwo).congr ?_⟩
    · intro u v
      simp only [Bool.false_eq_true, if_false, anySeen, seen_insert]
      tauto
    · intro u v
      simpa only [Bool.false_eq_true, if_false, if_true] using two_insert f s a ha u v

def different (f : Fin n → Option (Fin n)) : Pred n :=
  fun u v => f u ≠ none ∧ f v ≠ none ∧ f u ≠ f v

lemma distinctTags (A : Net n) (hz : Has A (fun _ _ => False)) (hr : ∀ i, Has A (lit i))
    (f : Fin n → Option (Fin n)) : ∃ B, Ext A B (4*n) ∧ Has B (different f) := by
  classical
  obtain ⟨B,e,h⟩ := packGroups A hz hr f Finset.univ
  obtain ⟨C,e',_,hTwo⟩ := scan B (e.2 _ hz) f (fun a => (h a).congr (by simp [group])) Finset.univ
  refine ⟨C, (e.trans e').weaken (by simp; omega), hTwo.congr ?_⟩
  intro u v
  cases hu : f u <;> cases hv : f v <;> simp [different, twoSeen, seen, hu, hv]

def paint (r : Fin n → ℕ) (p : Fin n → Option (Fin n)) (bound : ∀ i, r i < n)
    (inc : ∀ i j, p i = some j → r i < r j) (i : Fin n) : Bool :=
  match hp : p i with
  | none => false
  | some j => !(paint r p bound inc j)
termination_by n - r i
decreasing_by have := inc i j hp; have := bound j; omega

lemma paint_edge (r : Fin n → ℕ) (p : Fin n → Option (Fin n)) (bound : ∀ i, r i < n)
    (inc : ∀ i j, p i = some j → r i < r j) {i j} (h : p i = some j) :
    paint r p bound inc i ≠ paint r p bound inc j := by
  conv_lhs => rw [paint]
  split <;> simp_all

def center (p : Fin n → Option (Fin n)) (color : Fin n → Bool) (b : Bool) (i : Fin n) : Option (Fin n) :=
  some (if color i = b then (p i).getD i else i)
def leaves (color : Fin n → Bool) (b : Bool) (i : Fin n) : Option (Fin n) :=
  if color i = b then some i else none

def allows (p : Fin n → Option (Fin n)) (c : Fin n → Bool) (b : Bool) : Pred n :=
  fun u v => u ≠ v ∧ ¬(c u = b ∧ p u = some v) ∧ ¬(c v = b ∧ p v = some u)

lemma allows_iff (p : Fin n → Option (Fin n)) (c : Fin n → Bool)
    (proper : ∀ i j, p i = some j → c i ≠ c j) (b : Bool) (u v : Fin n) :
    (different (center p c b) u v ∨ different (leaves c b) u v) ↔ allows p c b u v := by
  have huv := proper u v
  have hvu := proper v u
  by_cases he : u = v
  · subst v; simp [different,allows]
  · by_cases hu : c u = b <;> by_cases hv : c v = b <;>
      cases hpu : p u <;> cases hpv : p v <;>
      simp_all [different, center, leaves, allows, eq_comm]

lemma star (A : Net n) (hz : Has A (fun _ _ => False)) (hr : ∀ i, Has A (lit i))
    (p : Fin n → Option (Fin n)) (c : Fin n → Bool) (proper : ∀ i j, p i = some j → c i ≠ c j)
    (b : Bool) : ∃ B, Ext A B (8*n+1) ∧ Has B (allows p c b) := by
  obtain ⟨B,e,hC⟩ := distinctTags A hz hr (center p c b)
  obtain ⟨C,e',hL⟩ := distinctTags B (e.2 _ hz) (fun i => e.2 _ (hr i)) (leaves c b)
  obtain ⟨D,eD,hw⟩ := combine C (e'.2 _ hC) hL false
  exact ⟨D, ((e.trans e').trans eD).weaken (by omega), hw.congr (by simpa using allows_iff p c proper b)⟩

lemma buildAll {ι : Type} [DecidableEq ι] (A : Net n) (hz : Has A (fun _ _ => False))
    (hr : ∀ i, Has A (lit i)) {q : Pred n} (hq : Has A q)
    (p : ι → Fin n → Option (Fin n)) (c : ι → Fin n → Bool) (b : ι → Bool)
    (proper : ∀ t i j, p t i = some j → c t i ≠ c t j) (s : Finset ι) :
    ∃ B, Ext A B (s.card * (8*n+2)) ∧ Has B (fun u v => q u v ∧ ∀ t ∈ s, allows (p t) (c t) (b t) u v) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨A, by simpa using Ext.refl A, hq.congr (by simp)⟩
  | @insert t s ht ih =>
    obtain ⟨B,e,h⟩ := ih
    obtain ⟨C,e',hs⟩ := star B (e.2 _ hz) (fun i => e.2 _ (hr i)) (p t) (c t) (proper t) (b t)
    obtain ⟨D,eD,hw⟩ := combine C (e'.2 _ h) hs true
    refine ⟨D, ((e.trans e').trans eD).weaken (by rw [Finset.card_insert_of_notMem ht, Nat.add_mul]; omega), hw.congr ?_⟩
    intro u v
    simp only [if_true, Finset.forall_mem_insert]
    tauto

def neighbors (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n)) (i : Fin n) :=
  Finset.univ.filter fun j : Fin n => r i < r j ∧ (G i j = true ∨ G j i = true)

noncomputable def parent {d : ℕ} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n))
    (t : Fin d) (i : Fin n) : Option (Fin n) := (neighbors G r i).toList[t.val]?

lemma parent_mem {d : ℕ} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n))
    (t : Fin d) {i j} (hp : parent G r t i = some j) : j ∈ neighbors G r i :=
  Finset.mem_toList.mp (List.mem_of_getElem? hp)

lemma parent_iff {d : ℕ} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n))
    (hd : ∀ i, (neighbors G r i).card ≤ d) (i j : Fin n) :
    (∃ t : Fin d, parent G r t i = some j) ↔ r i < r j ∧ (G i j = true ∨ G j i = true) := by
  constructor
  · rintro ⟨t,ht⟩
    exact (Finset.mem_filter.mp (parent_mem G r t ht)).2
  · intro h
    have hm : j ∈ (neighbors G r i).toList := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    obtain ⟨k,hk,he⟩ := List.getElem_of_mem hm
    have hk' : k < d := lt_of_lt_of_le (by simpa using hk : k < (neighbors G r i).card) (hd i)
    exact ⟨⟨k,hk'⟩, by simpa [parent, List.getElem?_eq_getElem hk] using congrArg some he⟩

lemma construct (n d : ℕ) (G : Fin n → Fin n → Bool) (rank : Equiv.Perm (Fin n))
    (hd : ∀ i, (neighbors G rank i).card ≤ d) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.output < n + D.size ∧
      D.size ≤ 8 * (n+1) * (2*d+1) + 2 ∧
      ∀ u v : Fin n, D.eval (input u v) = decide (u ≠ v ∧ G u v = false ∧ G v u = false) := by
  classical
  let p := @parent n d G rank
  let r := fun i : Fin n => (rank i).val
  have hbound : ∀ i, r i < n := fun i => (rank i).isLt
  have hinc (t : Fin d) (i j : Fin n) (hp : p t i = some j) : r i < r j :=
    (Finset.mem_filter.mp (parent_mem G rank t hp)).2.1
  let c := fun t : Fin d => paint r (p t) hbound (hinc t)
  have hproper (t : Fin d) (i j : Fin n) (hp : p t i = some j) : c t i ≠ c t j :=
    paint_edge r (p t) hbound (hinc t) hp
  obtain ⟨A,hA,hz,hr⟩ := seed n
  obtain ⟨B,e,hq⟩ := distinctTags A hz hr some
  have hneq : Has B (fun u v => u ≠ v) := hq.congr (by simp [different])
  obtain ⟨C,e',hw⟩ := buildAll B (e.2 _ hz) (fun i => e.2 _ (hr i)) hneq
    (ι := Fin d × Bool) (fun t => p t.1) (fun t => c t.1) Prod.snd (fun t => hproper t.1) Finset.univ
  obtain ⟨w,hwlt,he⟩ := hw
  refine ⟨⟨C.gs,w⟩, C.mono,C.back, hwlt, ?_, ?_⟩
  · change C.gs.length ≤ _
    have h1 := e.1
    have h2 := e'.1
    simp at h2
    nlinarith
  · intro u v
    have hm : (u ≠ v ∧ ∀ t : Fin d × Bool, t ∈ Finset.univ → allows (p t.1) (c t.1) t.2 u v) ↔
        u ≠ v ∧ G u v = false ∧ G v u = false := by
      have hf := parent_iff G rank hd u v
      have hb := parent_iff G rank hd v u
      change (∃ t, p t u = some v) ↔ _ at hf
      change (∃ t, p t v = some u) ↔ _ at hb
      constructor
      · rintro ⟨hne, hall⟩
        have neverUV (t : Fin d) := (hall (t,c t u) (Finset.mem_univ _)).2.1
        have neverVU (t : Fin d) := (hall (t,c t v) (Finset.mem_univ _)).2.2
        have hruv : rank u ≠ rank v := fun h => hne (rank.injective h)
        rcases lt_or_gt_of_ne hruv with hlt | hlt
        · have hnot : ¬(G u v = true ∨ G v u = true) := by
            intro h
            obtain ⟨t,ht⟩ := hf.mpr ⟨hlt,h⟩
            exact neverUV t ⟨rfl,ht⟩
          cases hu : G u v <;> cases hv : G v u <;> simp_all
        · have hnot : ¬(G v u = true ∨ G u v = true) := by
            intro h
            obtain ⟨t,ht⟩ := hb.mpr ⟨hlt,h⟩
            exact neverVU t ⟨rfl,ht⟩
          cases hu : G u v <;> cases hv : G v u <;> simp_all
      · rintro ⟨hne,hu,hv⟩
        refine ⟨hne, fun t _ => ⟨hne, ?_, ?_⟩⟩
        · rintro ⟨_,h⟩
          simpa [hu,hv] using (hf.mp ⟨t.1,h⟩).2
        · rintro ⟨_,h⟩
          simpa [hu,hv] using (hb.mp ⟨t.1,h⟩).2
    change (vals C.gs u v).getD w false = _
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using (he u v).trans hm

end Absent

namespace Builder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open scoped Classical

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_init (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_init [] gs x i (by simpa using hi)
  simpa [run] using this

abbrev Signal := (ℕ → Bool) → Bool

def basis (g : Gate) : Prop := (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧
    g.inputs.length ≤ 2 ∧ (g.op=.not → g.inputs.length=1)

def ordered (p : ℕ) (gs : List Gate) : Prop :=
  ∀ j (h : j < gs.length), ∀ i ∈ gs[j].inputs, i < p+j

def pins (w : ℕ) (gs : List Gate) : ℕ := (gs.map (fun g => g.inputs.count w)).sum
def negs (gs : List Gate) : ℕ :=
  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  (gs.filter (fun g => decide (g.op=.not))).length
theorem negs_append (gs hs : List Gate) : negs (gs++hs) = negs gs + negs hs := by simp [negs]
def delta (i j : ℕ) : ℕ := if i=j then 1 else 0

theorem ordered_cat {p : ℕ} {gs hs : List Gate} (h : ordered p gs)
    (j : ordered (p+gs.length) hs) : ordered p (gs++hs) := by
  intro k hk i hi
  rw [List.getElem_append] at hi
  split_ifs at hi with lt
  · exact h k lt i hi
  · have e := j (k-gs.length) (by simp at hk; omega) i hi
    omega

theorem ordered_single {p : ℕ} {g : Gate} (h : ∀ i ∈ g.inputs, i<p) : ordered p [g] := by
  intro j hj i hi
  have : j=0 := by simp at hj; omega
  subst j
  simpa using h i hi

theorem run_cat (gs hs : List Gate) (xs : List Bool) : run (gs++hs) xs = run hs (run gs xs) := by
  simp [run,List.foldl_append]

def Builds (M : ℕ) (f : Signal) (cost inv : ℕ) (uses : ℕ → ℕ) : Prop :=
  ∀ start, M ≤ start → ∃ (gs : List Gate) (o : ℕ),
    gs.length ≤ cost ∧ negs gs ≤ inv ∧ (∀ g∈gs, basis g) ∧ ordered start gs ∧
    o < start+gs.length ∧
    (∀ i<M, pins i gs + delta o i ≤ uses i) ∧
    ∀ (v : ℕ → Bool) (xs : List Bool), xs.length=start →
      (∀ i<M, xs.getD i false=v i) → (run gs xs).getD o false = f v

theorem leaf (M i : ℕ) (hi : i<M) : Builds M (fun v => v i) 0 0 (delta i) := by
  intro start hs
  refine ⟨[],i,by simp,by simp [negs],by simp,by intro j hj; simp at hj,by simp; omega,?_,?_⟩
  · simp [pins]
  · intro v xs _ hv; exact hv i hi

theorem falseGate (M : ℕ) : Builds M (fun _ => false) 1 0 (fun _ => 0) := by
  intro start hs
  refine ⟨[⟨.or,[]⟩],start,by simp,by simp [negs],by simp [basis],
    ordered_single (by simp),by simp,?_,?_⟩
  · intro i hi; simp [pins,delta,show start≠i by omega]
  · intro v xs h _; rw [←h]; simp [run,GateOp.eval]

theorem binary {M : ℕ} {f h : Signal} {s t nf nh : ℕ} {u v : ℕ → ℕ}
    (hf : Builds M f s nf u) (hh : Builds M h t nh v) (op : GateOp)
    (hop : op=.or ∨ op=.and) :
    Builds M (fun x => op.eval [f x,h x]) (s+t+1) (nf+nh) (fun i => u i+v i) := by
  intro start hs
  obtain ⟨l,a,lc,ln,lb,lo,la,lp,lv⟩ := hf start hs
  obtain ⟨r,b,rc,rn,rb,ro,ra,rp,rv⟩ := hh (start+l.length) (by omega)
  let out := start+l.length+r.length
  let g : Gate := ⟨op,[a,b]⟩
  have gn : op≠.not := by rcases hop with e|e <;> simp [e]
  have gm : basis g := by rcases hop with e|e <;> simp [g,basis,e]
  have gg : ∀ w∈g.inputs, w<start+(l++r).length := by
    intro w hw; simp only [g,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl <;> simp <;> omega
  refine ⟨(l++r)++[g],out,by simp; omega,?_,?_,ordered_cat (ordered_cat lo ro) (ordered_single gg),by simp [out]; omega,?_,?_⟩
  · simp only [negs,List.filter_append,List.length_append] at *
    simp [g,gn]; omega
  · intro gate hg
    simp only [List.mem_append,List.mem_singleton] at hg
    rcases hg with (e|e)|rfl
    · exact lb gate e
    · exact rb gate e
    · exact gm
  · intro i hi
    have lpi := lp i hi; have rpi := rp i hi
    have eq : delta out i=0 := by simp [out,delta,show start+l.length+r.length≠i by omega]
    have one : [a,b].count i = delta a i + delta b i := by
      by_cases ax : a=i <;> by_cases bx : b=i <;> simp [delta,ax,bx,eq_comm]
    simp only [pins] at lpi rpi
    simp only [pins,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,g,eq,one]
    omega
  · intro val xs hxs hval
    have llen : (run l xs).length=start+l.length := by rw [run_length,hxs]
    have lrlen : (run (l++r) xs).length=out := by simp [out,run_length,hxs]; omega
    have left : (run (l++r) xs).getD a false=f val :=
      (run_init l r xs a (by rwa [hxs])).trans (lv val xs hxs hval)
    have right : (run (l++r) xs).getD b false=h val := by
      rw [run_cat]
      exact rv val _ llen (fun i hi => (run_input l xs i (by omega)).trans (hval i hi))
    rw [run_snoc,←lrlen,getD_at]
    change op.eval [(run (l++r) xs).getD a false,(run (l++r) xs).getD b false] = _
    rw [left,right]

theorem inverter {M : ℕ} {f : Signal} {s k : ℕ} {u : ℕ → ℕ} (hf : Builds M f s k u) :
    Builds M (fun x => !(f x)) (s+1) (k+1) u := by
  intro start hs
  obtain ⟨gs,a,c,n,b,o,ha,p,v⟩ := hf start hs
  let g : Gate := ⟨.not,[a]⟩
  let out := start+gs.length
  refine ⟨gs++[g],out,by simp; omega,?_,?_,ordered_cat o (ordered_single (by simpa [g] using ha)),
    by simp [out],?_,?_⟩
  · simpa [negs,g] using Nat.add_le_add_right n 1
  · intro gate hg
    rcases List.mem_append.mp hg with h | h
    · exact b _ h
    · have := List.mem_singleton.mp h; subst gate; simp [basis,g]
  · intro i hi
    have hp := p i hi
    have ne : out≠i := by dsimp [out]; omega
    by_cases e : a=i <;> simpa [pins,g,delta,ne,e,eq_comm] using hp
  · intro val xs hx agree
    have hlen : (run gs xs).length=out := by simp [run_length,hx,out]
    rw [run_snoc,←hlen,getD_at]
    change Bool.not ((run gs xs).getD a false) = Bool.not (f val)
    rw [v val xs hx agree]

theorem join_two {M : ℕ} {f h : Signal} {s t p q : ℕ} {u v : ℕ → ℕ}
    (hf : Builds M f s p u) (hh : Builds M h t q v) :
    Builds M (fun x => f x || h x) (s+t+1) (p+q) (fun i => u i+v i) := by
  simpa [GateOp.eval] using binary hf hh .or (Or.inl rfl)

theorem meet_two {M : ℕ} {f h : Signal} {s t p q : ℕ} {u v : ℕ → ℕ}
    (hf : Builds M f s p u) (hh : Builds M h t q v) :
    Builds M (fun x => f x && h x) (s+t+1) (p+q) (fun i => u i+v i) := by
  simpa [GateOp.eval] using binary hf hh .and (Or.inr rfl)

theorem more {M : ℕ} {f : Signal} {s t p q : ℕ} {u v : ℕ → ℕ}
    (hf : Builds M f s p u) (hs : s≤t) (hn : p≤q) (hu : ∀ i<M, u i≤v i) :
    Builds M f t q v := by
  intro start h
  obtain ⟨gs,o,a,b,c,d,e,g,k⟩ := hf start h
  exact ⟨gs,o,a.trans hs,b.trans hn,c,d,e,fun i hi => (g i hi).trans (hu i hi),k⟩

theorem joins {α : Type} {M : ℕ} (l : List α) (f : α → Signal) (price inv : α → ℕ)
    (u : α → ℕ → ℕ) (nonempty : l≠[]) (h : ∀ a∈l, Builds M (f a) (price a) (inv a) (u a)) :
    Builds M (fun x => l.any fun a => f a x) ((l.map price).sum + (l.length-1)) (l.map inv).sum
      (fun i => (l.map (fun a => u a i)).sum) := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    by_cases hl : l=[]
    · subst l; simpa using ha
    · have hb := ih hl (fun b hb => h b (List.mem_cons_of_mem _ hb))
      have total : price a + ((l.map price).sum + (l.length-1)) + 1 =
          ((a::l).map price).sum + ((a::l).length-1) := by
        have hl' : 0<l.length := List.length_pos_iff.mpr hl
        simp; omega
      have combined := join_two ha hb
      rw [total] at combined
      simpa using combined

noncomputable def collective {α : Type} (l : Finset α) (f : α → Signal) : Signal :=
  fun x => decide (∃ i∈l, f i x=true)

theorem collect {α : Type} {M : ℕ} (l : Finset α) (f : α → Signal) (price inv : α → ℕ)
    (u : α → ℕ → ℕ) (nonempty : l.Nonempty) (h : ∀ a∈l, Builds M (f a) (price a) (inv a) (u a)) :
    Builds M (collective l f) ((∑ i∈l, price i)+(l.card-1)) (∑ i∈l, inv i)
      (fun w => ∑ i∈l, u i w) := by
  classical
  have e : (fun v => l.toList.any (fun i => f i v)) = collective l f := by
    funext v; apply Bool.eq_iff_iff.mpr; simp [collective]
  have hh := joins l.toList f price inv u (by simpa using nonempty.ne_empty) (by simpa using h)
  rw [e] at hh
  simpa only [Finset.sum_map_toList,Finset.length_toList] using hh

private theorem wires_append (gs hs : List Gate) (out : ℕ) (x : List Bool) :
    (⟨gs ++ hs, out⟩ : Circuit).wires x =
      hs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        ((⟨gs, 0⟩ : Circuit).wires x) := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_length (gs : List Gate) (out : ℕ) (x : List Bool) :
    ((⟨gs, out⟩ : Circuit).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires, List.foldl_append] at ih ⊢
    omega

private theorem wires_getD_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) :
    ((⟨gs ++ hs, 0⟩ : Circuit).wires x).getD i false =
      ((⟨gs, 0⟩ : Circuit).wires x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    have hlen : i < ((⟨gs ++ hs, 0⟩ : Circuit).wires x).length := by
      rw [wires_length, List.length_append]; omega
    rw [← List.append_assoc, wires_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD]
    exact ih

private theorem map_gates_sim (L1 M : ℕ) (ρ : ℕ → ℕ) (gs : List Gate) (x W2 : List Bool)
    (hxlen : x.length = L1)
    (hM : W2.length + gs.length ≤ M)
    (hρ_in : ∀ i < L1, (ρ i < W2.length ∧ W2.getD (ρ i) false = x.getD i false) ∨
                       (M ≤ ρ i ∧ x.getD i false = false))
    (hρ_ge : ∀ i, L1 ≤ i → ρ i = i - L1 + W2.length) :
    ∀ (i : ℕ),
      ((⟨gs.map (fun g => ⟨g.op, g.inputs.map ρ⟩), 0⟩ : Circuit).wires W2).getD (ρ i) false =
        ((⟨gs, 0⟩ : Circuit).wires x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    simp only [List.map_nil, Circuit.wires, List.foldl_nil]
    by_cases hi : i < L1
    · rcases hρ_in i hi with ⟨_, heq⟩ | ⟨hge, hfalse⟩
      · exact heq
      · have : W2.length ≤ ρ i := by simp at hM; omega
        rw [hfalse, List.getD_eq_getElem?_getD, List.getElem?_eq_none this]; rfl
    · have h1 : L1 ≤ i := by omega
      have h2 : W2.length ≤ ρ i := by rw [hρ_ge i h1]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : x.length ≤ i),
        List.getElem?_eq_none h2]
  | append_singleton gs g ih =>
    intro i
    have hM' : W2.length + gs.length ≤ M := by simp at hM; omega
    have ih' := ih hM'
    set gs' : List Gate := gs.map (fun g => ⟨g.op, g.inputs.map ρ⟩)
    set g' : Gate := ⟨g.op, g.inputs.map ρ⟩
    have hmap : (gs ++ [g]).map (fun g => ⟨g.op, g.inputs.map ρ⟩) = gs' ++ [g'] := by
      simp [gs', g']
    rw [hmap, wires_append, wires_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set W1 := (⟨gs, 0⟩ : Circuit).wires x
    set W2' := (⟨gs', 0⟩ : Circuit).wires W2
    have hW1len : W1.length = L1 + gs.length := by rw [wires_length, hxlen]
    have hW2'len : W2'.length = W2.length + gs.length := by
      rw [wires_length]; simp [gs']
    have hval_eq : g'.op.eval (g'.inputs.map fun k => W2'.getD k false) =
        g.op.eval (g.inputs.map fun k => W1.getD k false) := by
      simp only [g', List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _
      exact ih' k
    rw [hval_eq]
    by_cases hi_lt : i < L1 + gs.length
    · by_cases h1 : i < L1
      · rcases hρ_in i h1 with ⟨hρlt, _⟩ | ⟨hρge, hfalse⟩
        · have hL : ∀ (l : List Bool) (a : Bool) (k : ℕ), k < l.length →
              (l ++ [a]).getD k false = l.getD k false := by
            intro l a k hk
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]
          rw [hL W2' _ (ρ i) (by omega), hL W1 _ i (by omega)]
          exact ih' i
        · have hW2_ge : (W2' ++ [g.op.eval (g.inputs.map fun k => W1.getD k false)]).length ≤ ρ i := by
            simp only [List.length_append, List.length_singleton, hW2'len]
            simp at hM; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hW2_ge]
          simp only [Option.getD_none]
          have hW1_get : (W1 ++ [g.op.eval (g.inputs.map fun k => W1.getD k false)]).getD i false = x.getD i false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < W1.length),
              ← List.getD_eq_getElem?_getD]
            have hpre := wires_getD_prefix [] gs x i (by simpa [hxlen] using h1)
            simpa [W1, Circuit.wires] using hpre
          rw [hW1_get, hfalse]
      · have hρi_lt : ρ i < W2'.length := by rw [hρ_ge i (by omega)]; omega
        have hL : ∀ (l : List Bool) (a : Bool) (k : ℕ), k < l.length →
            (l ++ [a]).getD k false = l.getD k false := by
          intro l a k hk
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]
        rw [hL W2' _ (ρ i) hρi_lt, hL W1 _ i (by omega)]
        exact ih' i
    · by_cases hi_eq : i = L1 + gs.length
      · subst hi_eq
        have hρi_eq : ρ (L1 + gs.length) = W2'.length := by
          rw [hρ_ge _ (by omega)]; omega
        rw [hρi_eq, ← hW1len]
        simp [List.getD_eq_getElem?_getD]
      · have hρi_gt : W2'.length + 1 ≤ ρ i := by
          rw [hρ_ge i (by omega)]; omega
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp [hW1len]; omega : (W1 ++ [_]).length ≤ i),
          List.getElem?_eq_none (by simp [hW2'len]; omega : (W2' ++ [_]).length ≤ ρ i)]

theorem pins_zero (w : ℕ) (gs : List Gate) :
    pins w gs=0 ↔ ∀ g∈gs, w∉g.inputs := by
  induction gs with
  | nil => simp [pins]
  | cons g gs ih =>
    change g.inputs.count w + pins w gs = 0 ↔ _
    simp [ih,List.count_eq_zero]

theorem zero_negs (gs : List Gate) (h : ∀ g∈gs, g.op≠.not) : negs gs=0 := by
  induction gs with
  | nil => simp [negs]
  | cons g gs ih =>
    have n := h g List.mem_cons_self
    have t := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simpa [negs,n] using t

theorem ordered_circuit {p : ℕ} (C : Circuit) (back : ordered p C.gates) : ReadsBack p C := by
  intro j hj i hi
  have atg : gateAt C j=C.gates[j] := List.getD_eq_getElem _ _ hj
  exact back j hj i (atg ▸ hi)

end Builder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Builder
open scoped Classical

def shifted (k : ℕ) (gs : List Gate) := gs.map fun g => (⟨g.op,g.inputs.map (k+·)⟩ : Gate)

theorem run_shift (gs : List Gate) (pref body : List Bool) :
    run (shifted pref.length gs) (pref++body) = pref ++ run gs body := by
  induction gs using List.reverseRecOn with
  | nil => simp [shifted,run]
  | append_singleton gs g ih =>
    have h : shifted pref.length (gs++[g]) = shifted pref.length gs ++ [⟨g.op,g.inputs.map (pref.length+·)⟩] := by simp [shifted]
    rw [h,run_snoc,run_snoc,ih,List.append_assoc]
    congr 2
    simp [List.map_map,Function.comp_def,List.getD_eq_getElem?_getD,List.getElem?_append]

lemma shift_negs (k : ℕ) (gs : List Gate) : negs (shifted k gs) = negs gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change negs ([⟨g.op,g.inputs.map (k+·)⟩] ++ shifted k gs) = negs ([g]++gs)
    rw [negs_append,negs_append,ih]
    by_cases h : g.op=GateOp.not <;> simp [negs,h]

lemma shift_props (k n : ℕ) (gs : List Gate) (ord : ordered n gs) (bs : ∀ g∈gs, basis g) :
    ordered (k+n) (shifted k gs) ∧ (∀ g∈shifted k gs, basis g) ∧
    negs (shifted k gs) = negs gs ∧ ∀ i<k, pins i (shifted k gs) = 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj i hi
    have hj' : j < gs.length := by simpa [shifted] using hj
    simp only [shifted,List.getElem_map] at hi
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    have := ord j hj' a ha
    omega
  · intro g hg
    simp only [shifted,List.mem_map] at hg
    obtain ⟨a,ha,rfl⟩ := hg
    simpa [basis] using bs a ha
  · exact shift_negs k gs
  · intro i hi
    apply (pins_zero _ _).mpr
    intro g hg hread
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    obtain ⟨j,_,he⟩ := List.mem_map.mp hread
    omega

def pairGate {n : ℕ} (mate : Equiv.Perm (Fin n)) (i : Fin n) : Gate :=
  ⟨.or,[i.val,n+(mate i).val]⟩
def tapGate (w : ℕ) (on : Prop) [Decidable on] : Gate :=
  ⟨.or,if on then [w] else []⟩

def pre {n : ℕ} (mate : Equiv.Perm (Fin n)) (rows cols : Finset (Fin n)) :=
  (List.ofFn fun i : Fin n => tapGate i.val (i∈rows)) ++
  (List.ofFn fun i : Fin n => tapGate (n+(mate i).val) (i∈cols)) ++
  List.ofFn (pairGate mate)

def rawOnly (k : ℕ) (gs : List Gate) := ∀ g∈gs, ∀ i∈g.inputs, i<k
lemma raw_run (gs : List Gate) (x : List Bool) (h : rawOnly x.length gs) :
    run gs x = x ++ gs.map (fun g => g.op.eval (g.inputs.map fun i => x.getD i false)) := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    have h' : rawOnly x.length gs := fun a ha => h a (List.mem_append_left _ ha)
    rw [run_snoc,ih h']
    simp only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.append_cancel_left_eq]
    congr 2
    apply List.map_congr_left
    intro i hi
    exact Absent.getLeft _ _ _ _ (h g (by simp) i hi)

lemma pre_raw {n} (m : Equiv.Perm (Fin n)) (r c : Finset (Fin n)) : rawOnly (2*n) (pre m r c) := by
  intro g hg j hj
  simp only [pre,List.mem_append,List.mem_ofFn] at hg
  rcases hg with (⟨i,rfl⟩|⟨i,rfl⟩)|⟨i,rfl⟩
  · by_cases h : i∈r <;> simp [tapGate,h] at hj <;> have := i.isLt <;> omega
  · by_cases h : i∈c <;> simp [tapGate,h] at hj <;> have := (m i).isLt <;> omega
  · have := i.isLt; have := (m i).isLt
    simp [pairGate] at hj
    omega

lemma pre_basis {n} (m : Equiv.Perm (Fin n)) (r c : Finset (Fin n)) : ∀ g∈pre m r c, basis g := by
  intro g hg
  simp only [pre,List.mem_append,List.mem_ofFn] at hg
  rcases hg with (⟨i,rfl⟩|⟨i,rfl⟩)|⟨i,rfl⟩
  · by_cases h : i∈r <;> simp [basis,tapGate,h]
  · by_cases h : i∈c <;> simp [basis,tapGate,h]
  · simp [basis,pairGate]

def rowBits {n} (r : Finset (Fin n)) (u : Fin n) := List.ofFn fun i => decide (i∈r ∧ i=u)
def pairBits {n} (u v : Fin n) := List.ofFn fun i => decide (i=u ∨ i=v)
def input {n} (m : Equiv.Perm (Fin n)) (u v : Fin n) := PEqualNP.Represents.oneEach u (m v)

lemma pre_eval {n} (m : Equiv.Perm (Fin n)) (r c : Finset (Fin n)) (u v : Fin n) :
    run (pre m r c) (input m u v) = input m u v ++ (rowBits r u ++ rowBits c v) ++ pairBits u v := by
  have h := pre_raw m r c
  have len : (input m u v).length=2*n := by simp [input,PEqualNP.Represents.oneEach]; omega
  rw [raw_run _ _ (by rwa [len])]
  have lv (i : Fin n) : (input m u v).getD i.val false = decide (i=u) := by
    apply Bool.eq_iff_iff.mpr
    rw [input,Crossed.oe_getD,decide_eq_true_eq]
    have := i.isLt
    simp only [Fin.ext_iff]
    omega
  have rv (i : Fin n) : (input m u v).getD (n+(m i).val) false = decide (i=v) := by
    apply Bool.eq_iff_iff.mpr
    rw [input,Crossed.oe_getD,decide_eq_true_eq]
    have := u.isLt
    have hmi : (m i).val = (m v).val ↔ i=v := Fin.ext_iff.symm.trans m.injective.eq_iff
    omega
  let ev := fun g : Gate => g.op.eval (g.inputs.map fun i => (input m u v).getD i false)
  have er : (List.ofFn fun i : Fin n => tapGate i.val (i∈r)).map ev = rowBits r u := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn; funext i
    by_cases h : i∈r <;> simp [ev,Function.comp_def,tapGate,h,GateOp.eval,rowBits,lv,-List.getD_eq_getElem?_getD]
  have ec : (List.ofFn fun i : Fin n => tapGate (n+(m i).val) (i∈c)).map ev = rowBits c v := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn; funext i
    by_cases h : i∈c <;> simp [ev,Function.comp_def,tapGate,h,GateOp.eval,rowBits,rv,-List.getD_eq_getElem?_getD]
  have ep : (List.ofFn (pairGate m)).map ev = pairBits u v := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn; funext i
    simp [ev,Function.comp_def,pairGate,GateOp.eval,lv,rv,-List.getD_eq_getElem?_getD]
  change input m u v ++ (pre m r c).map ev = _
  simp only [pre,List.map_append,er,ec,ep,List.append_assoc]

abbrev Ix (n d : ℕ) := Fin n ⊕ ((Fin n × Fin d) × Bool)

noncomputable def edge {n d} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n)) : Ix n d → Fin n × Fin n
  | .inl i => (i,i)
  | .inr ((i,t),b) =>
    let j := (Absent.parent G r t i).getD i
    if b then (j,i) else (i,j)

def small {n} (G : Fin n → Fin n → Bool) (a b : Fin n) := a=b ∨ G a b=true ∨ G b a=true
lemma edge_iff {n d} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n))
    (hd : ∀ i, (Absent.neighbors G r i).card ≤ d) (a b : Fin n) :
    (∃ t : Ix n d, edge G r t=(a,b)) ↔ small G a b := by
  constructor
  · rintro ⟨i|⟨⟨i,t⟩,c⟩,h⟩
    · simp [edge] at h; exact Or.inl (h.1.symm.trans h.2)
    · cases hp : Absent.parent G r t i with
      | none => cases c <;> simp [edge,hp] at h <;> exact Or.inl (h.1.symm.trans h.2)
      | some j =>
        have hn := ((Absent.parent_iff G r hd i j).mp ⟨t,hp⟩).2
        cases c <;> simp [edge,hp] at h <;> unfold small <;> grind
  · rintro (h|h)
    · exact ⟨.inl a,by simp [edge,h]⟩
    · by_cases e : a=b
      · exact ⟨.inl a,by simp [edge,e]⟩
      rcases lt_or_gt_of_ne (fun eq => e (r.injective eq)) with lt | gt
      · obtain ⟨t,ht⟩ := (Absent.parent_iff G r hd a b).mpr ⟨lt,h⟩
        exact ⟨.inr ((a,t),false),by simp [edge,ht]⟩
      · obtain ⟨t,ht⟩ := (Absent.parent_iff G r hd b a).mpr ⟨gt,h.symm⟩
        exact ⟨.inr ((b,t),true),by simp [edge,ht]⟩

def forbidden {n} (G : Fin n → Fin n → Bool) (u v : Fin n) :=
  u≠v ∧ G u v=false ∧ G v u=false
noncomputable def entries {n d} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n))
    (R C : Finset (Fin n)) (k : ℕ) : Finset (Ix n d) :=
  Finset.univ.filter fun t => Tags.tag G R C (edge G r t).1 (edge G r t).2=k
def chosen {n d} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n))
    (R C : Finset (Fin n)) (k : ℕ) (u v : Fin n) :=
  ∃ t ∈ @entries n d G r R C k, Tags.isOn R C (edge G r t).1 (edge G r t).2 u v

lemma choice_iff {n d} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n))
    (hd : ∀ i, (Absent.neighbors G r i).card ≤ d) (R C : Finset (Fin n)) (k : ℕ) (u v : Fin n) :
    @chosen n d G r R C k u v ↔ ∃ a b, small G a b ∧ Tags.tag G R C a b=k ∧ Tags.isOn R C a b u v := by
  constructor
  · rintro ⟨t,ht,hon⟩
    exact ⟨_,_,(edge_iff G r hd _ _).mp ⟨t,rfl⟩,(Finset.mem_filter.mp ht).2,hon⟩
  · rintro ⟨a,b,hab,htag,hon⟩
    obtain ⟨t,ht⟩ := (edge_iff G r hd a b).mpr hab
    refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩ <;> simpa [ht]

lemma sparse_correct {n d} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n))
    (hd : ∀ i, (Absent.neighbors G r i).card ≤ d) (R C : Finset (Fin n))
    (cover : ∀ i j, G i j=true → G j i=false → i∈R ∨ j∈C ∨ j∈R ∨ i∈C) (u v : Fin n) :
    G u v=true ↔ @chosen n d G r R C 0 u v ∨
      (@chosen n d G r R C 1 u v ∧ ¬(@chosen n d G r R C 2 u v ∨ forbidden G u v)) := by
  rw [Tags.correct G R C cover, choice_iff G r hd, choice_iff G r hd, choice_iff G r hd]
  have pos (a b : Fin n) (h : Tags.tag G R C a b=0 ∨ Tags.tag G R C a b=1) : small G a b := by
    rcases h with h|h
    · exact Or.inr (Or.inl (Tags.tag0 G R C a b h).1)
    · exact Or.inr (Or.inl (Tags.tag1 G R C a b h).1)
  have neg : (∃ a b, Tags.tag G R C a b=2 ∧ Tags.isOn R C a b u v) ↔
      (∃ a b, small G a b ∧ Tags.tag G R C a b=2 ∧ Tags.isOn R C a b u v) ∨ forbidden G u v := by
    constructor
    · rintro ⟨a,b,hk,hon⟩
      by_cases h : small G a b
      · exact Or.inl ⟨a,b,h,hk,hon⟩
      · right
        have hab := Tags.isOn_gen R C a b u v hon
        unfold small at h
        unfold forbidden
        grind
    · rintro (⟨a,b,_,ht,hon⟩|⟨hne,hg,hg'⟩)
      · exact ⟨a,b,ht,hon⟩
      · exact ⟨u,v,Tags.tag2' G R C u v hg hne,Tags.isOn_self R C u v⟩
  rw [neg]
  constructor
  · rintro (⟨a,b,h,hon⟩|⟨⟨a,b,h,hon⟩,hn⟩)
    · exact Or.inl ⟨a,b,pos a b (Or.inl h),h,hon⟩
    · exact Or.inr ⟨⟨a,b,pos a b (Or.inr h),h,hon⟩,hn⟩
  · rintro (⟨a,b,_,h,hon⟩|⟨⟨a,b,_,h,hon⟩,hn⟩)
    · exact Or.inl ⟨a,b,h,hon⟩
    · exact Or.inr ⟨⟨a,b,h,hon⟩,hn⟩

lemma card_entries {n d} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n)) (R C : Finset (Fin n)) :
    (@entries n d G r R C 0).card + (@entries n d G r R C 1).card + (@entries n d G r R C 2).card ≤ n+2*n*d := by
  classical
  unfold entries
  rw [Finset.card_filter,Finset.card_filter,Finset.card_filter,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _ : Ix n d, 1 := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs <;> omega
    _ = _ := by simp [Ix]; ring

def wire {n} (s : Fin 3 × Fin n) : ℕ := if s.1=0 then 2*n+s.2.val else if s.1=1 then s.2.val else n+s.2.val
lemma wire_lt {n} (s : Fin 3 × Fin n) : wire s < 3*n := by
  have := s.2.isLt
  unfold wire; split_ifs <;> omega
noncomputable def term {n d : ℕ} (G : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n)) (R C : Finset (Fin n)) (t : Ix n d) : Signal :=
  let ab := edge G r t
  let ij := Tags.tm R C ab.1 ab.2
  fun x => x (wire ij.1) && x (wire ij.2)
def Frag (M : ℕ) (f : Signal) (cost inv : ℕ) := ∃ uses, Builds M f cost inv uses
lemma atom {M i : ℕ} (h : i<M) : Frag M (fun x => x i) 0 0 := ⟨_,leaf M i h⟩
lemma fOr {M s t a b} {f g : Signal} (hf : Frag M f s a) (hg : Frag M g t b) :
    Frag M (fun x => f x || g x) (s+t+1) (a+b) := by
  obtain ⟨_,h⟩ := hf; obtain ⟨_,k⟩ := hg; exact ⟨_,join_two h k⟩
lemma fAnd {M s t a b} {f g : Signal} (hf : Frag M f s a) (hg : Frag M g t b) :
    Frag M (fun x => f x && g x) (s+t+1) (a+b) := by
  obtain ⟨_,h⟩ := hf; obtain ⟨_,k⟩ := hg; exact ⟨_,meet_two h k⟩
lemma fNot {M s a} {f : Signal} (hf : Frag M f s a) : Frag M (fun x => !(f x)) (s+1) (a+1) := by
  obtain ⟨_,h⟩ := hf; exact ⟨_,inverter h⟩

lemma fSet {α : Type} {M} (s : Finset α) (f : α → Signal) (h : ∀ a∈s, Frag M (f a) 1 0) :
    Frag M (collective s f) (2*s.card+1) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : collective ∅ f = fun _ => false := by funext x; simp [collective]
    simpa only [he,Finset.card_empty,Nat.mul_zero,Nat.zero_add] using (show Frag M (fun _ => false) 1 0 from ⟨_,falseGate M⟩)
  | @insert a s ha ih =>
    have fr := fOr (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    have he : (fun x => f a x || collective s f x) = collective (insert a s) f := by
      funext x; apply Bool.eq_iff_iff.mpr; simp [collective]
    rw [he] at fr
    convert fr using 1 <;> rw [Finset.card_insert_of_notMem ha] <;> omega

lemma pins_cat (w : ℕ) (a b : List Gate) : pins w (a++b)=pins w a+pins w b := by simp [pins]
lemma pins_fn {n} (w : ℕ) (f : Fin n → Gate) :
    pins w (List.ofFn f) = ∑ i, (f i).inputs.count w := by simp [pins,List.sum_ofFn,Function.comp_def]

lemma pre_pins {n} (m : Equiv.Perm (Fin n)) (r c : Finset (Fin n)) (i : Fin n) :
    pins i.val (pre m r c) = 1 + (if i∈r then 1 else 0) ∧
    pins (n+(m i).val) (pre m r c) = 1 + (if i∈c then 1 else 0) := by
  classical
  have cl (k j : Fin n) : n+(m k).val ≠ j.val := by have := j.isLt; omega
  have eqr (k j : Fin n) : k.val=j.val ↔ k=j := Fin.ext_iff.symm
  have eqc (k j : Fin n) : n+(m k).val=n+(m j).val ↔ k=j :=
    Nat.add_left_cancel_iff.trans (Fin.ext_iff.symm.trans m.injective.eq_iff)
  let row := fun k : Fin n => tapGate k.val (k∈r)
  let col := fun k : Fin n => tapGate (n+(m k).val) (k∈c)
  have rr (k) : (row k).inputs.count i.val = if k=i then (if i∈r then 1 else 0) else 0 := by
    by_cases h : k=i <;> by_cases hr : k∈r <;> simp_all [row,tapGate,List.count_cons,eqr,eq_comm]
  have rc (k) : (row k).inputs.count (n+(m i).val)=0 := by
    by_cases h : k∈r <;> simp [row,tapGate,h,List.count_cons,cl,Ne.symm (cl i k)]
  have cr (k) : (col k).inputs.count i.val=0 := by
    by_cases h : k∈c <;> simp [col,tapGate,h,List.count_cons,cl,Ne.symm (cl k i)]
  have cc (k) : (col k).inputs.count (n+(m i).val) = if k=i then (if i∈c then 1 else 0) else 0 := by
    by_cases h : k=i <;> by_cases hc : k∈c <;> simp_all [col,tapGate,List.count_cons,eqc,eq_comm]
  have pr (k) : (pairGate m k).inputs.count i.val = if k=i then 1 else 0 := by
    by_cases h : k=i <;> simp [pairGate,List.count_cons,cl,Ne.symm (cl k i),eqr,h,eq_comm]
  have pc (k) : (pairGate m k).inputs.count (n+(m i).val) = if k=i then 1 else 0 := by
    by_cases h : k=i
    · subst k; simp [pairGate,cl,Ne.symm (cl i i)]
    · have ne := mt (eqc k i).mp h
      simp [pairGate,List.count_cons,h,ne,Ne.symm ne,cl,Ne.symm (cl i k),m.injective.ne h]
      exact fun e => h (m.injective (Fin.ext e))
  change pins i.val (List.ofFn row ++ List.ofFn col ++ List.ofFn (pairGate m)) = _ ∧ pins (n+(m i).val) (List.ofFn row ++ List.ofFn col ++ List.ofFn (pairGate m)) = _
  simp [pins_cat,pins_fn,rr,cc,rc,cr,pr,pc,Nat.add_comm]

lemma pre_negs {n} (m : Equiv.Perm (Fin n)) (r c : Finset (Fin n)) : negs (pre m r c) = 0 := by
  apply zero_negs
  intro g hg
  simp only [pre,List.mem_append,List.mem_ofFn] at hg
  rcases hg with (⟨i,rfl⟩|⟨i,rfl⟩)|⟨i,rfl⟩ <;> simp [tapGate,pairGate]

lemma reads_eq (C : Circuit) (w : ℕ) : readsIn C (Finset.range C.size) w = pins w C.gates := by
  let gs := C.gates
  have aux (l : List Gate) : (∑ j ∈ Finset.range l.length, (l.getD j ⟨.or,[]⟩).inputs.count w) = pins w l := by
    induction l using List.reverseRecOn with
    | nil => simp [pins]
    | append_singleton l g ih =>
      rw [List.length_append,List.length_singleton,Finset.sum_range_succ,pins_cat,←ih]
      rw [Absent.getLast]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [Absent.getLeft _ _ _ _ (Finset.mem_range.mp hj)]
  exact aux C.gates

lemma positive_pin (C : Circuit) (i : ℕ) (g : Gate) (hg : g∈C.gates) (hi : i∈g.inputs) : 0 < pins i C.gates := by
  by_contra h
  have hz : pins i C.gates=0 := by omega
  exact ((pins_zero _ _).mp hz g hg) hi

lemma necessity {n} (G : Fin n → Fin n → Bool) (m : Equiv.Perm (Fin n)) (R T : Finset (Fin n))
    (C : Circuit) (back : ReadsBack (2*n) C) (rep : PEqualNP.Represents.Represents G C)
    (hout : 2*n ≤ C.output) (use : ∀ i : Fin n,
      (∃ g∈C.gates, g.op=.or ∧ (g.inputs=[i.val,n+(m i).val] ∨ g.inputs=[n+(m i).val,i.val])) ∧
      pins i.val C.gates ≤ 1 + (if i∈R then 1 else 0) ∧
      pins (n+(m i).val) C.gates ≤ 1 + (if i∈T then 1 else 0)) :
    ∀ i j, G i (m j)=true → G j (m i)=false → i∈R ∨ j∈T ∨ j∈R ∨ i∈T := by
  intro i j hij hji
  by_contra! h
  have hne : i≠j := by rintro rfl; simp_all
  have pos (t : Fin n) : 0 < pins t.val C.gates ∧ 0 < pins (n+(m t).val) C.gates := by
    obtain ⟨g,hg,_,hg'⟩ := (use t).1
    constructor <;> apply positive_pin C _ g hg <;> rcases hg' with e|e <;> simp [e]
  have ai := (use i).2; have aj := (use j).2
  have pi := pos i; have pj := pos j
  have hn := Crossed.main_aux n n G C i j (m i) (m j) hne (m.injective.ne hne)
    (by simpa [two_mul] using back) rep (use i).1 (use j).1
  have eq := hn (by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rw [reads_eq]
    simp [h.1,h.2.1,h.2.2.1,h.2.2.2] at ai aj
    rcases hk with rfl|rfl|rfl|rfl <;> omega) (by
      have := i.isLt; have := j.isLt; have := (m i).isLt; have := (m j).isLt
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      omega)
  simp_all

def logicBits {n} (R C : Finset (Fin n)) (D : Circuit) (u v : Fin n) :=
  (rowBits R u ++ rowBits C v) ++ D.wires (pairBits u v)
lemma logic_len {n} (R C : Finset (Fin n)) (D : Circuit) (u v : Fin n) :
    (logicBits R C D u v).length = 3*n+D.size := by
  change ((rowBits R u ++ rowBits C v) ++ run D.gates (pairBits u v)).length=_
  simp [run_length,rowBits,pairBits,Circuit.size]; omega

lemma getAfter {α : Type} (l r : List α) (i : ℕ) (d : α) : (l++r).getD (l.length+i) d = r.getD i d := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append]

def evalWire (l : List Bool) : ℕ → Bool := fun i => l.getD i false
lemma sig_wire {n} (R C : Finset (Fin n)) (D : Circuit) (s : Fin 3 × Fin n) (u v : Fin n) :
    evalWire (logicBits R C D u v) (wire s)=true ↔ s ∈ Tags.sigs R C u v := by
  rcases s with ⟨k,a⟩
  have hk : k=0 ∨ k=1 ∨ k=2 := by fin_cases k <;> decide
  have getpair : (D.wires (pairBits u v)).getD a.val false = decide (a=u ∨ a=v) := by
    change (run D.gates (pairBits u v)).getD a.val false = _
    rw [run_input _ _ _ (by simp [pairBits])]
    simp [pairBits,List.getD_eq_getElem?_getD,a.isLt]
  rcases hk with rfl|rfl|rfl
  · rw [Tags.mem0]
    have hh : 2*n = (rowBits R u ++ rowBits C v).length := by simp [rowBits]; omega
    simp only [evalWire,logicBits,wire,ite_true,hh,getAfter,getpair,decide_eq_true_eq]
  · rw [Tags.mem1]
    simp [evalWire,logicBits,wire,rowBits,List.getD_eq_getElem?_getD,List.getElem?_append,a.isLt]
  · rw [Tags.mem2]
    simp [evalWire,logicBits,wire,rowBits,List.getD_eq_getElem?_getD,List.getElem?_append,a.isLt]

noncomputable def decoded {n d : ℕ} (A : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n)) (R C : Finset (Fin n))
    (abs : ℕ) : Signal :=
  let f := @term n d A r R C
  let h := fun k => collective (@entries n d A r R C k) f
  fun x => h 0 x || (h 1 x && !(h 2 x || x abs))

lemma decoder {n d M} (A : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n)) (R C : Finset (Fin n))
    (abs : ℕ) (hm : 3*n≤M) (hab : abs<M) :
    Frag M (@decoded n d A r R C abs) (2*(n+2*n*d)+7) 1 := by
  let ss := @entries n d A r R C
  let f := @term n d A r R C
  have single (a : Ix n d) : Frag M (f a) 1 0 := by
    let t := Tags.tm R C (edge A r a).1 (edge A r a).2
    exact fAnd (atom (lt_of_lt_of_le (wire_lt t.1) hm)) (atom (lt_of_lt_of_le (wire_lt t.2) hm))
  have collect' (k : ℕ) := fSet (M:=M) (ss k) f (fun a _ => single a)
  have tt := fOr (collect' 0) (fAnd (collect' 1) (fNot (fOr (collect' 2) (atom hab))))
  obtain ⟨uses,b⟩ := tt
  refine ⟨uses,more b ?_ (by decide) (fun _ _ => le_rfl)⟩
  have count := @card_entries n d A r R C
  change (ss 0).card + (ss 1).card + (ss 2).card ≤ _ at count
  omega

lemma eval_dec {n d} (A : Fin n → Fin n → Bool) (r : Equiv.Perm (Fin n)) (R C : Finset (Fin n))
    (hd : ∀ i, (Absent.neighbors A r i).card≤d) (D : Circuit)
    (hD : ∀ u v, D.eval (pairBits u v)=decide (forbidden A u v))
    (cover : ∀ i j, A i j=true → A j i=false → i∈R ∨ j∈C ∨ j∈R ∨ i∈C) (u v : Fin n) :
    @decoded n d A r R C (2*n+D.output) (evalWire (logicBits R C D u v))=A u v := by
  let x := evalWire (logicBits R C D u v)
  have h (k : ℕ) : collective (@entries n d A r R C k) (@term n d A r R C) x=true ↔ @chosen n d A r R C k u v := by
    simp only [collective,decide_eq_true_eq,chosen,term, Bool.and_eq_true,x,sig_wire,Tags.isOn]
  have ab : x (2*n+D.output)=true ↔ forbidden A u v := by
    have len : (rowBits R u ++ rowBits C v).length=2*n := by simp [rowBits]; omega
    change ((rowBits R u ++ rowBits C v) ++ D.wires (pairBits u v)).getD _ false = true ↔ _
    rw [←len]
    rw [getAfter]
    change D.eval (pairBits u v)=true ↔ _
    rw [hD]; simp
  apply Bool.eq_iff_iff.mpr
  change (_ || (_ && !(_ || x (2*n+D.output))))=true ↔ _
  rw [Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',Bool.or_eq_false_iff]
  have result := sparse_correct A r hd R C cover u v
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  grind

lemma make {n d} (G : Fin n → Fin n → Bool) (m r : Equiv.Perm (Fin n)) (R T : Finset (Fin n))
    (hd : ∀ i, (Absent.neighbors (fun i j => G i (m j)) r i).card≤d)
    (cover : ∀ i j, G i (m j)=true → G j (m i)=false → i∈R ∨ j∈T ∨ j∈R ∨ i∈T) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (2*n) C ∧ PEqualNP.Represents.Represents G C ∧
      PEqualNP.NotBracket.notCount C ≤ 1 ∧ (∀ g∈C.gates,g.op=.not → g.inputs.length=1) ∧
      2*n≤C.output ∧ C.output<2*n+C.size ∧ C.size≤n+24*(n+1)*(d+1) ∧ ∀ i : Fin n,
        (∃ g∈C.gates,g.op=.or ∧ (g.inputs=[i.val,n+(m i).val] ∨ g.inputs=[n+(m i).val,i.val])) ∧
        pins i.val C.gates ≤ 1+(if i∈R then 1 else 0) ∧ pins (n+(m i).val) C.gates ≤ 1+(if i∈T then 1 else 0) := by
  classical
  let A := fun i j : Fin n => G i (m j)
  obtain ⟨D,dm,db,dv,ds,de⟩ := Absent.construct n d A r hd
  let P := pre m R T
  let V := shifted (4*n) D.gates
  let M := 3*n+D.size
  have da : 2*n+D.output<M := by dsimp [M]; omega
  obtain ⟨_,ed⟩ := decoder (d:=d) A r R T (2*n+D.output) (M:=M) (by dsimp [M]; omega) da
  obtain ⟨qs,o,cost,invs,qbasis,qorder,ov,_,qeval⟩ := ed M le_rfl
  let Q := shifted (2*n) qs
  let gs := (P++V)++Q
  let C : Circuit := ⟨gs,2*n+o⟩
  have lp : P.length=3*n := by simp [P,pre]; omega
  have lv : V.length=D.size := by simp [V,shifted,Circuit.size]
  have lq : Q.length=qs.length := by simp [Q,shifted]
  have lc : C.size=3*n+D.size+qs.length := by simp [C,Circuit.size,gs,lp,lv,lq,Nat.add_assoc]
  have pord : ordered (2*n) P := by
    intro j hj i hi
    have := pre_raw m R T P[j] (List.getElem_mem _) i hi
    omega
  have dor : ordered n D.gates := by
    intro j hj i hi
    apply db j hj
    simpa only [gateAt,List.getD_eq_getElem _ _ hj] using hi
  have dbasis (g) (h : g∈D.gates) : basis g := by
    obtain ⟨hop,len⟩ := dm g h
    change (g.op=.and ∨ g.op=.or) at hop
    rcases hop with eq|eq <;> simp [basis,eq,len]
  obtain ⟨vord,vbasis,vneg,vpins⟩ := shift_props (4*n) n D.gates dor dbasis
  obtain ⟨qord,qb,qn,qp⟩ := shift_props (2*n) M qs qorder qbasis
  have bas (g : Gate) (hg : g∈gs) : basis g := by
    rcases List.mem_append.mp hg with h|h
    · rcases List.mem_append.mp h with h|h
      · exact pre_basis m R T _ h
      · exact vbasis _ h
    · exact qb _ h
  have dn : negs D.gates=0 := by
    apply zero_negs
    intro g hg
    obtain ⟨h,_⟩ := dm g hg
    change g.op=.and ∨ g.op=.or at h
    rcases h with h|h <;> simp [h]
  have pn := pre_negs m R T
  have out (u v : Fin n) : C.eval (input m u v) = A u v := by
    let x := input m u v
    let z := rowBits R u ++ rowBits T v
    let paired := pairBits u v
    let L := logicBits R T D u v
    have hx : x.length=2*n := by simp [x,input,PEqualNP.Represents.oneEach]; omega
    have hxz : (x++z).length=4*n := by simp [z,rowBits,hx]; omega
    have pe : run P x=(x++z)++paired := pre_eval m R T u v
    have ve : run V ((x++z)++paired)=(x++z)++D.wires paired := by
      dsimp only [V]; rw [←hxz]; exact run_shift _ _ _
    have qe : run Q (x++L)=x++run qs L := by
      dsimp only [Q]; rw [←hx]; exact run_shift _ _ _
    have vals : run gs x=x++run qs L := by
      rw [show gs=(P++V)++Q from rfl,run_cat,run_cat,pe,ve,List.append_assoc]
      exact qe
    have hl : L.length=M := logic_len R T D u v
    have ev := qeval (evalWire L) L hl (fun _ _ => rfl)
    change (run gs x).getD (2*n+o) false=_
    rw [vals,←hx]
    rw [getAfter]
    have complete (a b : Fin n) : D.eval (pairBits a b) = decide (forbidden A a b) := by
      rw [show pairBits a b = Absent.input a b from rfl,de]
      exact congrArg (fun h : Decidable (a≠b ∧ A a b=false ∧ A b a=false) => @decide _ h) (Subsingleton.elim _ _)
    exact ev.trans (eval_dec A r R T hd D complete cover u v)
  have rawpins (w : ℕ) (hw : w<2*n) : pins w gs=pins w P := by
    have hv := vpins w (by omega)
    have hq := qp w hw
    simp only [gs,pins_cat]
    change pins w P + pins w (shifted (4*n) D.gates) + pins w (shifted (2*n) qs) = _
    omega
  refine ⟨C, ?_, ?_, ?_, ?_, ?_, by change 2*n≤2*n+o; omega, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨hop,hlen,_⟩ := bas g hg
    exact ⟨hop,hlen⟩
  · apply ordered_circuit
    apply ordered_cat (ordered_cat pord ?_) ?_
    · simpa only [lp,show 2*n+3*n=4*n+n by omega] using vord
    · simpa only [List.length_append,lp,lv,M,show 2*n+(3*n+D.size)=2*n+(3*n+D.size) from rfl] using qord
  · intro u v
    simpa [input,A] using out u (m.symm v)
  · change negs gs≤1
    rw [show gs=(P++V)++Q from rfl,negs_append,negs_append]
    change negs (pre m R T)+negs (shifted (4*n) D.gates)+negs (shifted (2*n) qs) ≤ 1
    omega
  · exact fun g hg => (bas g hg).2.2
  · change 2*n+o<2*n+C.size
    rw [lc]
    dsimp [M] at ov
    omega
  · rw [lc]
    nlinarith
  · intro i
    have h := pre_pins m R T i
    have ex : pairGate m i ∈ P := List.mem_append_right _ (List.mem_ofFn.mpr ⟨_,rfl⟩)
    refine ⟨⟨pairGate m i,List.mem_append_left _ (List.mem_append_left _ ex),rfl,Or.inl rfl⟩,?_,?_⟩
    · change pins i.val gs≤_; rw [rawpins _ (by have := i.isLt; omega)]; exact h.1.le
    · change pins (n+(m i).val) gs≤_; rw [rawpins _ (by have := (m i).isLt; omega)]; exact h.2.le

end PEqualNP.Outside.L_meta_25540_aux

theorem PEqualNP.Outside.L_meta_25540 : (∀ (n d : ℕ) (G : Fin n → Fin n → Bool) (mate rank : Equiv.Perm (Fin n))
    (rows cols : Finset (Fin n)),
  let A := fun (i j : Fin n) => G i (mate j)
  let cover := ∀ i j, A i j = true → A j i = false →
    i ∈ rows ∨ j ∈ cols ∨ j ∈ rows ∨ i ∈ cols
  (∀ v : Fin n, (Finset.univ.filter (fun later : Fin n =>
    rank v < rank later ∧ (A v later = true ∨ A later v = true))).card ≤ d) →
  (cover ↔ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n) C ∧
    PEqualNP.Represents.Represents G C ∧
    PEqualNP.NotBracket.notCount C ≤ 1 ∧
    (∀ g ∈ C.gates, g.op = .not → g.inputs.length = 1) ∧
    2 * n ≤ C.output ∧ C.output < 2 * n + C.size ∧
    C.size ≤ n + 24 * (n + 1) * (d + 1) ∧
    ∀ i : Fin n,
      (∃ g ∈ C.gates, g.op = .or ∧
        (g.inputs = [i.val, n + (mate i).val] ∨
         g.inputs = [n + (mate i).val, i.val])) ∧
      (C.gates.map (fun g => g.inputs.count i.val)).sum ≤
        1 + (if i ∈ rows then 1 else 0) ∧
      (C.gates.map (fun g => g.inputs.count (n + (mate i).val))).sum ≤
        1 + (if i ∈ cols then 1 else 0))) := by
  intro n d G mate rank rows cols A cover hd
  constructor
  · exact PEqualNP.Outside.L_meta_25540_aux.make G mate rank rows cols hd
  · rintro ⟨C,_,back,rep,_,_,hout,_,_,use⟩
    exact PEqualNP.Outside.L_meta_25540_aux.necessity G mate rows cols C back rep hout use
