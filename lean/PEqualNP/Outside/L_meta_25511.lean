import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25511_aux.Cross

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
end PEqualNP.Outside.L_meta_25511_aux.Cross

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def graph (m : Nat) (u v : Fin (2*m)) : Bool :=
  let i := u.val / 2
  let j := v.val / 2
  let offset := if v.val % 2 = 0 then 1 else 2 + u.val % 2
  decide (i = j ∨ i = (j + offset) % m)

namespace Rows

def point {m : Nat} (i : Fin m) (b : Bool) : Fin (2*m) :=
  ⟨2*i.val+b.toNat,by have := i.isLt; cases b <;> simp <;> omega⟩

def group {m : Nat} (v : Fin (2*m)) : Fin m := ⟨v.val/2,by have := v.isLt;omega⟩

theorem pointGroup {m : Nat} (i : Fin m) (b : Bool) : (point i b).val/2 = i.val := by
  cases b <;> dsimp [point] <;> omega

theorem pointSide {m : Nat} (i : Fin m) (b : Bool) : (point i b).val %2 = b.toNat := by
  cases b <;> dsimp [point] <;> omega

def pairs (m : Nat) : (Fin m × Bool) ↪ Fin (2*m) where
  toFun p := point p.1 p.2
  inj' := by
    rintro ⟨i,b⟩ ⟨j,c⟩ e
    have v := congrArg Fin.val e
    change 2*i.val+b.toNat=2*j.val+c.toNat at v
    have eq : i=j := by apply Fin.ext; cases b <;> cases c <;> simp at v <;> omega
    subst j
    cases b <;> cases c <;> simp_all

def prev {m : Nat} (i : Fin m) (d : Nat) : Fin m :=
  ⟨(i.val+m-d)%m,Nat.mod_lt _ (by have := i.isLt;omega)⟩

private theorem modBack {m j d : Nat} (hj : j<m) (hd : d≤m) :
    ((j+d)%m+m-d)%m = j := by
  by_cases h : j+d<m
  · rw [Nat.mod_eq_of_lt h,show j+d+m-d=j+m by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hj]
  · rw [Nat.mod_eq_sub_mod (by omega : m≤j+d),Nat.mod_eq_of_lt (by omega : j+d-m<m),
      show j+d-m+m-d=j by omega,Nat.mod_eq_of_lt hj]

private theorem back {m d : Nat} {i j : Fin m} (hd : d≤m) (e : i.val=(j.val+d)%m) : j=prev i d := by
  apply Fin.ext
  change j.val = (i.val+m-d)%m
  rw [e,modBack j.isLt hd]

private theorem evenAt {m : Nat} (v : Fin (2*m)) (i : Fin m)
    (vi : group v=i) (b : v.val %2=0) : v=point i false := by
  subst i
  apply Fin.ext
  change v.val=2*(v.val/2)+0
  omega

private theorem oddAt {m : Nat} (v : Fin (2*m)) (i : Fin m)
    (vi : group v=i) (b : v.val %2≠0) : v=point i true := by
  subst i
  apply Fin.ext
  change v.val=2*(v.val/2)+1
  omega

theorem degreeLE {m : Nat} (hm : 5≤m) (u : Fin (2*m)) :
    (Finset.univ.filter (fun v : Fin (2*m) => graph m u v=true)).card ≤ 4 := by
  let i := group u
  let a := point i false
  let b := point i true
  let c := point (prev i 1) false
  let d := point (prev i (2+u.val %2)) true
  have sub : Finset.univ.filter (fun v : Fin (2*m) => graph m u v=true) ⊆ {a,b,c,d} := by
    intro v hv
    have hv' := of_decide_eq_true ((Finset.mem_filter.mp hv).2)
    change u.val/2=v.val/2 ∨ u.val/2=(v.val/2+(if v.val %2=0 then 1 else 2+u.val %2))%m at hv'
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rcases hv' with eq|offset
    · have vi : group v=i := Fin.ext eq.symm
      by_cases h : v.val %2=0
      · exact Or.inl (evenAt v i vi h)
      · exact Or.inr (Or.inl (oddAt v i vi h))
    · by_cases h : v.val %2=0
      · rw [if_pos h] at offset
        exact Or.inr (Or.inr (Or.inl (evenAt v _ (back (i:=i) (j:=group v) (by omega) offset) h)))
      · rw [if_neg h] at offset
        exact Or.inr (Or.inr (Or.inr (oddAt v _ (back (i:=i) (j:=group v) (by omega) offset) h)))
  have bound := Finset.card_le_card sub
  have q1 := Finset.card_insert_le a ({b,c,d} : Finset _)
  have q2 := Finset.card_insert_le b ({c,d} : Finset _)
  have q3 := Finset.card_insert_le c ({d} : Finset _)
  simp only [Finset.card_singleton] at q3
  omega

theorem rowClose {m : Nat} (hm : 5≤m) (i : Fin m) :
    (Finset.univ.filter (fun v : Fin (2*m) => graph m (pairs m (i,false)) v ≠
      graph m (pairs m (i,true)) v)).card ≤ 2 := by
  let a := point (prev i 2) true
  let b := point (prev i 3) true
  have sub : Finset.univ.filter (fun v : Fin (2*m) => graph m (pairs m (i,false)) v ≠ graph m (pairs m (i,true)) v) ⊆ {a,b} := by
    intro v hv
    have diff := (Finset.mem_filter.mp hv).2
    change graph m (point i false) v ≠ graph m (point i true) v at diff
    simp only [graph,pointGroup,pointSide,Bool.toNat_false,Bool.toNat_true,Nat.add_zero] at diff
    by_cases h : v.val %2=0
    · simp [h] at diff
    · by_cases h2 : i.val=(v.val/2+2)%m
      · exact Finset.mem_insert.mpr (Or.inl (oddAt v _ (back (j:=group v) (by omega) h2) h))
      · by_cases h3 : i.val=(v.val/2+3)%m
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (oddAt v _ (back (j:=group v) (by omega) h3) h)))
        · simp [h,h2,h3] at diff
  have uc := Finset.card_le_card sub
  have q := Finset.card_insert_le a ({b} : Finset _)
  simp only [Finset.card_singleton] at q
  omega

end Rows

def once {n : Nat} (C : Circuit) (π : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  let reads := readsIn C (Finset.range C.size)
  reads i.val=1 ∧ reads (n+(π i).val)=1 ∧
    ∃ g∈C.gates, g.op=.or ∧ (g.inputs=[i.val,n+(π i).val] ∨ g.inputs=[n+(π i).val,i.val])

theorem internalOutput {m : Nat} (hm : 5≤m) (C : Circuit) (rep : Represents (graph m) C) :
    (2*m)+(2*m)≤C.output := by
  by_contra! small
  have lit (u : Fin (2*m)) : C.output=u.val ∨ C.output=2*m+u.val := by
    have h : Cross.val C (oneEach u u) C.output = true :=
      (rep u u).trans (by simp [graph])
    rw [Cross.val_input (Cross.oe_len _ _ u u) small,Cross.oe_getD] at h
    exact h
  have a := lit ⟨0,by omega⟩
  have b := lit ⟨1,by omega⟩
  change C.output=0 ∨ C.output=2*m+0 at a
  change C.output=1 ∨ C.output=2*m+1 at b
  omega

theorem symmetric {m : Nat} (hm : 5≤m) (C : Circuit) (π : Equiv.Perm (Fin (2*m)))
    (back : ReadsBack (2*m+(2*m)) C) (rep : Represents (graph m) C)
    (u v : Fin (2*m)) (hu : once C π u) (hv : once C π v) :
    graph m u (π v) = graph m v (π u) := by
  by_cases same : u=v
  · rw [same]
  have ne := fun eq => same (π.injective eq)
  apply Cross.main_aux _ _ _ C u v (π u) (π v) same ne back rep hu.2.2 hv.2.2
  · intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl
    · exact hu.1
    · exact hv.1
    · exact hu.2.1
    · exact hv.2.1
  · have h := internalOutput hm C rep
    have a := u.isLt
    have b := v.isLt
    have c := (π u).isLt
    have d := (π v).isLt
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

namespace Col

private def group {m : ℕ} (v : Fin (2*m)) : Fin m := ⟨v.val/2, by omega⟩
private def shift {m : ℕ} (hm : 5 ≤ m) (v : Fin (2*m)) (t : Fin 2) : Fin m :=
  ⟨(v.val/2+(if v.val %2=0 then 1 else 2+t.val))%m, Nat.mod_lt _ (by omega)⟩
private def row {m : ℕ} (a : Fin m) (t : Fin 2) : Fin (2*m) := ⟨2*a.val+t.val,by omega⟩

private lemma edge {m : ℕ} (hm : 5 ≤ m) (v : Fin (2*m)) (a : Fin m) (t : Fin 2) :
    graph m (row a t) v = true ↔ a.val = (group v).val ∨ a.val = (shift hm v t).val := by
  have hd : (2*a.val+t.val)/2 = a.val := by omega
  have hr : (2*a.val+t.val)%2 = t.val := by omega
  simp [graph,row,group,shift,hd,hr]

private lemma wrap {x m : ℕ} (hm : 0<m) (bound : x<2*m) :
    x%m=x ∨ x%m+m=x := by
  by_cases h:x<m
  · left; exact Nat.mod_eq_of_lt h
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (show x-m<m by omega)]
    omega

private lemma triples {m a b p q x₀ x₁ y₀ y₁ : ℕ} (hm : 5≤m) (ha:a<m) (hb:b<m)
    (hp:p<2) (hq:q<2) (ne:a≠b ∨ p≠q)
    (h0:x₀<m) (h1:x₁<m) (h2:y₀<m) (h3:y₁<m)
    (xx0 : x₀ = a+(if p=0 then 1 else 2) ∨ x₀+m = a+(if p=0 then 1 else 2))
    (xx1 : x₁ = a+(if p=0 then 1 else 3) ∨ x₁+m = a+(if p=0 then 1 else 3))
    (yy0 : y₀ = b+(if q=0 then 1 else 2) ∨ y₀+m = b+(if q=0 then 1 else 2))
    (yy1 : y₁ = b+(if q=0 then 1 else 3) ∨ y₁+m = b+(if q=0 then 1 else 3)) :
    let A := a = b ∨ a = y₀
    let B := a = b ∨ a = y₁
    let C := x₀ = b ∨ x₀ = y₀
    let D := x₁ = b ∨ x₁ = y₁
    ¬(A ∧ B ∧ C) ∧ ¬(A ∧ B ∧ D) ∧ ¬(A ∧ C ∧ D) ∧ ¬(B ∧ C ∧ D) := by
  dsimp only
  interval_cases p <;> interval_cases q <;> norm_num at xx0 xx1 yy0 yy1 ne
  all_goals
    refine ⟨?_,?_,?_,?_⟩ <;> intro bad <;> omega

private def pick {m : ℕ} (hm : 5 ≤ m) (v : Fin (2*m)) : Fin 4 → Fin (2*m) :=
  ![row (group v) 0, row (group v) 1, row (shift hm v 0) 0, row (shift hm v 1) 1]

private lemma nonzeroShift {m : ℕ} (hm:5≤m) (v : Fin (2*m)) (t : Fin 2) :
    (group v).val ≠ (shift hm v t).val := by
  have h : v.val/2 < m := by omega
  let d := if v.val %2=0 then 1 else 2+t.val
  have small : 1 ≤ d ∧ d ≤ 3 := by dsimp [d]; split <;> omega
  change v.val/2 ≠ (v.val/2+d)%m
  have e := wrap (by omega:0<m) (show v.val/2+d<2*m by omega)
  omega

private theorem pick_inj {m : ℕ} (hm:5≤m) (v : Fin (2*m)) :
    Function.Injective (pick hm v) := by
  intro x y eq
  have h0 := nonzeroShift hm v 0
  have h1 := nonzeroShift hm v 1
  have e := congrArg Fin.val eq
  fin_cases x <;> fin_cases y <;> first | rfl | (exfalso; norm_num [pick,row] at e <;> omega)

private lemma twoFalse (P : Fin 4 → Prop)
    (bad : ¬(P 0 ∧ P 1 ∧ P 2) ∧ ¬(P 0 ∧ P 1 ∧ P 3) ∧
      ¬(P 0 ∧ P 2 ∧ P 3) ∧ ¬(P 1 ∧ P 2 ∧ P 3)) :
    ∃ i j : Fin 4, i ≠ j ∧ ¬P i ∧ ¬P j := by
  classical
  by_cases h0:P 0 <;> by_cases h1:P 1 <;> by_cases h2:P 2 <;> by_cases h3:P 3
  all_goals first
    | exact ⟨0,1,by decide,h0,h1⟩
    | exact ⟨0,2,by decide,h0,h2⟩
    | exact ⟨0,3,by decide,h0,h3⟩
    | exact ⟨1,2,by decide,h1,h2⟩
    | exact ⟨1,3,by decide,h1,h3⟩
    | exact ⟨2,3,by decide,h2,h3⟩
    | exact (bad.1 ⟨h0,h1,h2⟩).elim
    | exact (bad.2.1 ⟨h0,h1,h3⟩).elim
    | exact (bad.2.2.1 ⟨h0,h2,h3⟩).elim
    | exact (bad.2.2.2 ⟨h1,h2,h3⟩).elim

theorem colMiss {m : ℕ} (hm : 5≤m) (v w : Fin (2*m)) (ne:v≠w) :
    ∃ a b, a ≠ b ∧ graph m a v = true ∧ graph m a w = false ∧
      graph m b v = true ∧ graph m b w = false := by
  have other : (group v).val ≠ (group w).val ∨ v.val %2 ≠ w.val %2 := by
    by_contra! h
    apply ne
    apply Fin.ext
    obtain ⟨e,h⟩ := h
    change v.val/2 = w.val/2 at e
    omega
  have sh (z : Fin (2*m)) (t : Fin 2) :
      (shift hm z t).val = (group z).val+(if z.val %2=0 then 1 else 2+t.val) ∨
      (shift hm z t).val+m = (group z).val+(if z.val %2=0 then 1 else 2+t.val) := by
    apply wrap (by omega)
    have := (group z).isLt
    split <;> omega
  have h := triples hm (group v).isLt (group w).isLt
    (show v.val %2<2 by omega) (show w.val %2<2 by omega) other
    (shift hm v 0).isLt (shift hm v 1).isLt (shift hm w 0).isLt (shift hm w 1).isLt
    (sh v 0) (sh v 1) (sh w 0) (sh w 1)
  let P := fun i : Fin 4 => graph m (pick hm v i) w = true
  have bad : ¬(P 0 ∧ P 1 ∧ P 2) ∧ ¬(P 0 ∧ P 1 ∧ P 3) ∧
      ¬(P 0 ∧ P 2 ∧ P 3) ∧ ¬(P 1 ∧ P 2 ∧ P 3) := by
    have h0 : P 0 ↔ _ := edge hm w (group v) 0
    have h1 : P 1 ↔ _ := edge hm w (group v) 1
    have h2 : P 2 ↔ _ := edge hm w (shift hm v 0) 0
    have h3 : P 3 ↔ _ := edge hm w (shift hm v 1) 1
    rw [h0,h1,h2,h3]
    exact h
  have pos (i : Fin 4) : graph m (pick hm v i) v = true := by
    fin_cases i <;> simp [pick,edge hm]
  obtain ⟨i,j,ij,hi,hj⟩ := twoFalse P bad
  exact ⟨_,_,fun e => ij (pick_inj hm v e),pos i,Bool.eq_false_iff.mpr hi,
    pos j,Bool.eq_false_iff.mpr hj⟩
end Col

theorem colFar {m : ℕ} (hm:5≤m) (v w : Fin (2*m)) (ne:v≠w) :
    4 ≤ (Finset.univ.filter (fun r => graph m r v ≠ graph m r w)).card := by
  classical
  obtain ⟨a,b,ab,av,aw,bv,bw⟩ := Col.colMiss hm v w ne
  obtain ⟨c,d,cd,cw,cv,dw,dv⟩ := Col.colMiss hm w v ne.symm
  have ac : a≠c := by rintro rfl; simp_all
  have ad : a≠d := by rintro rfl; simp_all
  have bc : b≠c := by rintro rfl; simp_all
  have bd : b≠d := by rintro rfl; simp_all
  let T : Finset (Fin (2*m)) := {a,b,c,d}
  have sub : T ⊆ Finset.univ.filter (fun r => graph m r v ≠ graph m r w) := by
    intro r hr
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp_all
  have len : T.card=4 := by simp [T,ab,ac,ad,bc,bd,cd]
  exact len ▸ Finset.card_le_card sub

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

theorem packBound : ∀ (n m a gap : ℕ) (G : Fin n → Fin n → Bool)
    (rowPair : (Fin m × Bool) ↪ Fin n)
    (π : Equiv.Perm (Fin n)) (kept : Finset (Fin n)),
  let rowDistance := fun (firstRow secondRow : Fin n) =>
    (Finset.univ.filter (fun col : Fin n => G firstRow col ≠ G secondRow col)).card
  let colDistance := fun (firstCol secondCol : Fin n) =>
    (Finset.univ.filter (fun row : Fin n => G row firstCol ≠ G row secondCol)).card
  let minority := fun (line : Fin n) =>
    min (Finset.univ.filter (fun onCol : Fin n => G line onCol = true)).card
        (Finset.univ.filter (fun offCol : Fin n => G line offCol = false)).card
  (∀ i, rowDistance (rowPair (i, false)) (rowPair (i, true)) ≤ a) →
  (∀ b c, b ≠ c → a + gap ≤ colDistance b c) →
  (∀ u ∈ kept, ∀ v ∈ kept, G u (π v) = G v (π u)) →
  gap * m ≤ gap * (n - kept.card) +
    ∑ u ∈ Finset.univ \ kept, minority u := by
  intro n m a gap G rowPair π kept
  classical
  dsimp only
  intro hrow hcol hsym
  let p (i : Fin m) (b : Bool) := rowPair (i, b)
  let active := Finset.univ.filter (fun i : Fin m => p i false ∈ kept ∧ p i true ∈ kept)
  let lost := Finset.univ \ active
  let away := Finset.univ \ kept
  let D (i : Fin m) (u : Fin n) := G u (π (p i false)) ≠ G u (π (p i true))
  have lost_le : lost.card ≤ away.card := by
    let side (i : Fin m) : Bool := if p i false ∈ kept then true else false
    apply Finset.card_le_card_of_injOn (fun i => p i (side i))
    · intro i hi
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hnot := (Finset.mem_sdiff.mp hi).2
      by_cases h : p i false ∈ kept
      · simp only [side, if_pos h]
        exact fun ht => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, ht⟩)
      · simpa only [side, if_neg h] using h
    · intro i _ j _ he
      exact congrArg Prod.fst (rowPair.injective he)
  have cover : ∀ i ∈ active, gap ≤ (away.filter (D i)).card := by
    intro i hi
    obtain ⟨hl, hr⟩ := (Finset.mem_filter.mp hi).2
    have close : (kept.filter (D i)).card ≤ a := by
      apply le_trans _ (hrow i)
      apply Finset.card_le_card_of_injOn π _ π.injective.injOn
      intro u hu
      obtain ⟨hk, hd⟩ := Finset.mem_filter.mp hu
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change G u (π (p i false)) ≠ G u (π (p i true)) at hd
      rwa [hsym u hk _ hl, hsym u hk _ hr] at hd
    have distinct : π (p i false) ≠ π (p i true) := by
      intro he
      have hf : false = true := congrArg Prod.snd (rowPair.injective (π.injective he))
      cases hf
    have far : a + gap ≤ (Finset.univ.filter (D i)).card := hcol _ _ distinct
    have dis : Disjoint (away.filter (D i)) (kept.filter (D i)) :=
      Finset.sdiff_disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have whole : away ∪ kept = Finset.univ := Finset.sdiff_union_of_subset (Finset.subset_univ _)
    have splitCount : (away.filter (D i)).card + (kept.filter (D i)).card =
        (Finset.univ.filter (D i)).card := by
      rw [← Finset.card_union_of_disjoint dis, ← Finset.filter_union, whole]
    omega
  have per_color (u : Fin n) (b : Bool) :
      (active.filter (fun i => D i u)).card ≤
        (Finset.univ.filter (fun j => G u j = b)).card := by
    let side (i : Fin m) : Bool := if G u (π (p i false)) = b then false else true
    apply Finset.card_le_card_of_injOn (fun i => π (p i (side i)))
    · intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hd : G u (π (p i false)) ≠ G u (π (p i true)) := (Finset.mem_filter.mp hi).2
      by_cases h : G u (π (p i false)) = b
      · simpa only [side, if_pos h] using h
      · simp only [side, if_neg h]
        have other (x y z : Bool) (hxy : x ≠ y) (hxz : x ≠ z) : y = z := by
          cases x <;> cases y <;> cases z <;> simp_all
        exact other _ _ _ hd h
    · intro i _ j _ he
      exact congrArg Prod.fst (rowPair.injective (π.injective he))
  have enough : gap * active.card ≤ ∑ u ∈ away,
        min (Finset.univ.filter (fun j => G u j = true)).card
          (Finset.univ.filter (fun j => G u j = false)).card := by
    calc
      gap * active.card = ∑ _i ∈ active, gap := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ active, (away.filter (D i)).card := Finset.sum_le_sum cover
      _ = ∑ u ∈ away, (active.filter (fun i => D i u)).card :=
        by
          simp_rw [Finset.card_filter]
          exact Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun u _ => le_min (per_color u true) (per_color u false)
  have sizes : lost.card + active.card = m := by
    simpa [lost] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ active)
  have away_size : away.card = n - kept.card := by
    simp [away, Finset.card_sdiff_of_subset (Finset.subset_univ kept)]
  rw [away_size] at lost_le
  calc
    gap * m = gap * lost.card + gap * active.card := by rw [← Nat.mul_add, sizes]
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left gap lost_le) enough

end PEqualNP.Outside.L_meta_25511_aux

open PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_25511_aux

theorem bound503 :
∀ (m : ℕ), 5 ≤ m →
  let n := 2 * m
  let G := fun (u v : Fin n) =>
    let i := u.val / 2
    let j := v.val / 2
    let offset := if v.val % 2 = 0 then 1 else 2 + u.val % 2
    decide (i = j ∨ i = (j + offset) % m)
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (π : Equiv.Perm (Fin n)),
    let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
    let paired := fun (i : Fin n) =>
      let x := i.val
      let y := n + (π i).val
      reads x = 1 ∧ reads y = 1 ∧
      ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (g.inputs = [x, y] ∨ g.inputs = [y, x])
    let kept := @Finset.filter (Fin n) paired (fun _ => Classical.propDecidable _) Finset.univ
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + n) C →
    PEqualNP.Represents.Represents G C →
    m ≤ 3 * (n - kept.card) := by
  intro m hm n G C π reads paired kept back rep
  classical
  have member (i : Fin n) (hi : i∈kept) : paired i :=
    ((@Finset.mem_filter (Fin n) paired (fun j => Classical.propDecidable (paired j)) Finset.univ i).mp hi).2
  have symm (u : Fin n) (hu : u∈kept) (v : Fin n) (hv : v∈kept) : G u (π v)=G v (π u) := by
    exact symmetric hm C π back rep u v (member u hu) (member v hv)
  have estimate := packBound n m 2 2 G (Rows.pairs m) π kept
    (Rows.rowClose hm) (colFar hm) symm
  let lost := Finset.univ \ kept
  have nc : lost.card=n-kept.card := by
    simp [lost,Finset.card_sdiff_of_subset (Finset.subset_univ kept)]
  have payment :
      (∑ u ∈ lost, min (Finset.univ.filter (fun v : Fin n => G u v = true)).card
        (Finset.univ.filter (fun v : Fin n => G u v = false)).card) ≤ 4*(n-kept.card) := by
    calc
      _ ≤ ∑ _u ∈ lost, 4 := Finset.sum_le_sum (fun u _ => le_trans (min_le_left _ _) (Rows.degreeLE hm u))
      _ = _ := by simp [nc,Nat.mul_comm]
  dsimp only at estimate
  dsimp only [lost] at payment
  omega

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def read (C : Circuit) (w : Nat) := readsIn C (Finset.range C.size) w
def excess (N : Nat) (C : Circuit) := ∑ w ∈ Finset.range N, (read C w - 1)
def unary (C : Circuit) := (C.gates.filter (fun g => g.inputs.length == 1)).length
def mixed (N : Nat) (C : Circuit) :=
  (C.gates.filter (fun g => g.inputs.length == 2 && (g.inputs.filter (fun w => w<N)).length == 1)).length
def shapes (C : Circuit) : Prop := ∀ g ∈ C.gates,
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length=2) ∨ (g.op=GateOp.not ∧ g.inputs.length=1)
def live (N : Nat) (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length, N+j.val ≠ C.output → 0 < read C (N+j.val)

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem sum_get511 {α : Type} (f : α → Nat) (z : α) (l : List α) :
    (∑ j ∈ Finset.range l.length, f (l.getD j z)) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons,Finset.sum_range_succ']
    simp only [List.getD_cons_succ,List.getD_cons_zero,List.map_cons,List.sum_cons]
    omega

private theorem sum_arity511 (gs : List Gate) (shape : ∀g ∈ gs, g.inputs.length=2 ∨ g.inputs.length=1) :
    (gs.map (fun g => g.inputs.length)).sum + (gs.filter (fun g => g.inputs.length==1)).length =
      2*gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have tail := ih (fun x hx => shape x (by simp [hx]))
    rcases shape g (by simp) with h|h <;>
      simp [h,List.filter_cons] <;> omega

private theorem input_arities511 {N : Nat} {C : Circuit} (sh : shapes C) (back : ReadsBack N C) :
    (∑ w ∈ Finset.range (N+C.size),read C w) + unary C = 2*C.size := by
  classical
  have occ (j : Nat) (hj : j∈Finset.range C.size) :
      (∑ w ∈ Finset.range (N+C.size), (gateAt C j).inputs.count w) = (gateAt C j).inputs.length := by
    have sub : (gateAt C j).inputs.toFinset ⊆ Finset.range (N+C.size) := by
      intro w hw
      have jlt : j<C.size := Finset.mem_range.mp hj
      have bound := back j jlt w (List.mem_toFinset.mp hw)
      exact Finset.mem_range.mpr (by omega)
    calc
      _ = ∑ w ∈ (gateAt C j).inputs.toFinset, (gateAt C j).inputs.count w :=
        (Finset.sum_subset sub (fun w _ h => List.count_eq_zero.mpr (fun m => h (List.mem_toFinset.mpr m)))).symm
      _ = _ := List.sum_toFinset_count_eq_length _
  unfold read readsIn
  rw [Finset.sum_comm,Finset.sum_congr rfl occ]
  change (∑ j ∈ Finset.range C.gates.length, (C.gates.getD j ⟨.or,[]⟩).inputs.length) + _ = _
  rw [sum_get511 (fun g : Gate => g.inputs.length)]
  exact sum_arity511 _ (fun g hg => (sh g hg).imp And.right And.right)

private theorem internalUses511 {N : Nat} {C : Circuit} (hl : live N C) :
    C.size ≤ (∑ j ∈ Finset.range C.size, read C (N+j))+1 := by
  classical
  have one (j : Nat) (hj : j∈Finset.range C.size) :
      1 ≤ read C (N+j) + (if j=C.output-N then 1 else 0) := by
    by_cases e : j=C.output-N
    · simp [e]
    · simp only [if_neg e,Nat.add_zero]
      exact hl ⟨j,Finset.mem_range.mp hj⟩ (by dsimp;omega)
  have h := Finset.sum_le_sum one
  rw [Finset.sum_add_distrib] at h
  simp at h
  split_ifs at h <;> omega

private theorem excessCount511 (N : Nat) (C : Circuit) :
    N+excess N C = (∑ w ∈ Finset.range N, read C w) +
      ((Finset.range N).filter fun w => read C w=0).card := by
  classical
  calc
    _ = ∑ w ∈ Finset.range N, (1+(read C w-1)) := by simp [excess,Finset.sum_add_distrib]
    _ = ∑ w ∈ Finset.range N, (read C w + if read C w=0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> omega
    _ = _ := by rw [Finset.sum_add_distrib,Finset.card_filter]

theorem ledger511 {N : Nat} {C : Circuit} (sh : shapes C) (back : ReadsBack N C) (hl : live N C)
    (zero : ((Finset.range N).filter fun w => read C w=0).card ≤ 2) :
    N+excess N C+unary C ≤ C.size+3 := by
  have all := input_arities511 sh back
  rw [Finset.sum_range_add] at all
  have gate := internalUses511 hl
  have raw := excessCount511 N C
  omega

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

theorem price511 {m : Nat} (hm : 5≤m) (D : Circuit)
    (sh : shapes D) (back : ReadsBack (2*m+2*m) D) (rep : Represents (graph m) D)
    (hl : live (2*m+2*m) D)
    (zero : ((Finset.range (2*m+2*m)).filter fun w => read D w=0).card ≤ 2)
    (matchBound : ∃ π : Equiv.Perm (Fin (2*m)),
      2*(2*m-(@Finset.filter _ (once D π) (fun _=>Classical.propDecidable _) Finset.univ).card) ≤
      4+3*excess (2*m+2*m) D+unary D+mixed (2*m+2*m) D) :
    38*m ≤ 9*D.size+3*mixed (2*m+2*m) D+39 := by
  classical
  obtain ⟨π,matching⟩ := matchBound
  let kept := @Finset.filter _ (once D π) (fun _=>Classical.propDecidable _) Finset.univ
  have mass : m≤3*(2*m-kept.card) := bound503 m hm D π back rep
  have raw := ledger511 sh back hl zero
  change 2*(2*m-kept.card) ≤ 4+3*excess (2*m+2*m) D+unary D+mixed (2*m+2*m) D at matching
  omega

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux.PruneWire
open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

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

theorem getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

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

theorem main_fold2 (n m p : ℕ) (B : List Gate)
    (hB : ∀ g ∈ B, n + m ∉ g.inputs) (w w' : List Bool)
    (hl : w.length = w'.length + 1) (hm : n + m ≤ w'.length)
    (hI : ∀ i, i ≠ n + m → w.getD i false = w'.getD (eraseRedirect n m p i) false) :
    ∀ i, i ≠ n + m → (B.foldl step w).getD i false =
      ((B.map (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))).foldl step
        w').getD (eraseRedirect n m p i) false := by
  induction B generalizing w w' with
  | nil => simpa using hI
  | cons g B ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (by simp)
    apply ih (fun g' hg' => hB g' (by simp [hg']))
    · simp [step, hl]
    · simp [step]; omega
    · intro i hi
      simp only [step, getD_snoc, List.map_map]
      have hx : g.op.eval (g.inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map ((fun i => w'.getD i false) ∘ eraseRedirect n m p)) := by
        congr 1
        apply List.map_congr_left
        intro a ha
        exact hI a (fun h => hg (h ▸ ha))
      have hIi := hI i hi
      obtain ⟨r, hr⟩ : ∃ r, r = eraseRedirect n m p i := ⟨_, rfl⟩
      rw [← hr] at hIi ⊢
      unfold eraseRedirect at hr
      rw [if_neg hi] at hr
      by_cases h1 : i < w.length
      · have hr1 : r < w'.length := by split_ifs at hr <;> omega
        rw [if_pos h1, if_pos hr1]; exact hIi
      · rw [if_neg h1]
        by_cases h2 : i = w.length
        · have h4 : r = w'.length := by split_ifs at hr <;> omega
          rw [if_pos h2, if_neg (by omega), if_pos h4]
          exact hx
        · have h4 : w'.length < r := by split_ifs at hr <;> omega
          rw [if_neg h2, if_neg (by omega), if_neg (by omega)]

theorem split_fold (C : Circuit) (x : List Bool) (m : ℕ) (hm : m < C.gates.length) :
    C.gates.foldl step x = (C.gates.drop (m + 1)).foldl step
      (step ((C.gates.take m).foldl step x) C.gates[m]) := by
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by simp
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]

theorem unread (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hu : ∀ k, m < k → ∀ hk : k < C.gates.length, n + m ∉ C.gates[k].inputs)
    (x : List Bool) (hx : x.length = n) (i : ℕ) (hi : i ≠ n + m) :
    PEqualNP.LowMerge.wireVal C x i =
      PEqualNP.LowMerge.wireVal (eraseGate n C m p) x (eraseRedirect n m p i) := by
  simp only [PEqualNP.LowMerge.wireVal, wires_eq]
  rw [split_fold C x m hm]
  simp only [eraseGate, if_pos hm]
  rw [List.foldl_append]
  have hWA : (List.foldl step x (List.take m C.gates)).length = n + m := by
    rw [fold_len, hx, List.length_take]; omega
  apply main_fold2 n m p _ _ _ _ _ _ _ i hi
  · intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hg
    simp only [List.getElem_drop]
    exact hu _ (by omega) _
  · simp [step]
  · omega
  · intro j hj
    generalize List.foldl step x (List.take m C.gates) = WA at *
    unfold eraseRedirect
    rw [if_neg hj]
    simp only [step, getD_snoc, hWA]
    by_cases h3 : j < n + m
    · rw [if_pos h3, if_neg (by omega)]
    · rw [if_neg h3, if_neg hj, if_pos (by omega), getD_big _ _ (by omega)]


end PEqualNP.Outside.L_meta_25511_aux.PruneWire

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private theorem erase_dead {N : Nat} {C : Circuit} (sh : shapes C) (back : ReadsBack N C)
    (j : Fin C.gates.length) (unused : read C (N+j.val) = 0)
    (hout : N+j.val ≠ C.output) :
    let D := eraseGate N C j.val N
    shapes D ∧ ReadsBack N D ∧ D.size + 1 = C.size ∧ mixed N D ≤ mixed N C ∧
      ∀ x : List Bool, x.length = N → D.eval x = C.eval x := by
  let D := eraseGate N C j.val N
  let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect N j.val N)⟩
  have hgs : D.gates = C.gates.take j.val ++ (C.gates.drop (j.val+1)).map rename := by
    simp [D,eraseGate,j.isLt,rename]
  have hsz : D.gates.length+1 = C.gates.length := by
    rw [hgs,List.length_append,List.length_take,List.length_map,List.length_drop]
    omega
  have hu (t : Nat) (ht : t < C.gates.length) : N+j.val ∉ (gateAt C t).inputs := by
    intro hit
    have pos := List.count_pos_iff.mpr hit
    have le : (gateAt C t).inputs.count (N+j.val) ≤ read C (N+j.val) :=
      Finset.single_le_sum (f := fun l => (gateAt C l).inputs.count (N+j.val))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ht)
    omega
  refine ⟨?_, ?_, hsz, ?_, ?_⟩
  · intro g hg
    rw [hgs,List.mem_append] at hg
    rcases hg with h | h
    · exact sh _ (List.mem_of_mem_take h)
    · obtain ⟨g₀,h₀,rfl⟩ := List.mem_map.mp h
      simpa [rename] using sh _ (List.mem_of_mem_drop h₀)
  · intro t ht w hw
    change t < D.gates.length at ht
    change w ∈ (gateAt D t).inputs at hw
    have atEq (E : Circuit) (l : Nat) (hl : l < E.gates.length) :
        gateAt E l = E.gates[l] := by simp [gateAt,hl]
    rw [atEq D t ht] at hw
    have takeLen : (C.gates.take j.val).length = j.val := by simp [Nat.le_of_lt j.isLt]
    by_cases h : t < j.val
    · have same : D.gates[t] = C.gates[t]'(by omega) := by
        simp only [hgs,List.getElem_append_left (by omega : t < (C.gates.take j.val).length),
          List.getElem_take]
      rw [same,←atEq] at hw
      exact back t (by omega) w hw
    · have same : D.gates[t] = rename (gateAt C (t+1)) := by
        simp only [hgs,List.getElem_append_right (by omega : (C.gates.take j.val).length ≤ t),
          takeLen,List.getElem_map,List.getElem_drop]
        simp only [show j.val+1+(t-j.val) = t+1 by omega,atEq C (t+1) (by omega)]
      rw [same] at hw
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
      have early := back (t+1) (by omega) v hv
      have different : v ≠ N+j.val := fun e => hu (t+1) (by omega) (e ▸ hv)
      unfold eraseRedirect
      split_ifs <;> omega
  · let isMix (g : Gate) := g.inputs.length == 2 && (g.inputs.filter (fun w => w<N)).length == 1
    have raw (w : Nat) : decide (eraseRedirect N j.val N w < N) = decide (w<N) := by
      have eq : eraseRedirect N j.val N w < N ↔ w<N := by
        unfold eraseRedirect
        split_ifs <;> omega
      simp [eq]
    have countRaw (l : List Nat) :
        ((l.map (eraseRedirect N j.val N)).filter (fun w => w<N)).length =
          (l.filter (fun w => w<N)).length := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [List.map_cons,List.filter_cons,raw]
        split <;> simp [ih]
    have isSame (g : Gate) : isMix (rename g) = isMix g := by simp [isMix,rename,countRaw]
    have countMix (l : List Gate) : ((l.map rename).filter isMix).length =
        (l.filter isMix).length := by
      induction l with
      | nil => rfl
      | cons g l ih =>
        simp only [List.map_cons,List.filter_cons,isSame]
        split <;> simp [ih]
    change (D.gates.filter isMix).length ≤ (C.gates.filter isMix).length
    rw [hgs,List.filter_append,List.length_append,countMix]
    have splitC : C.gates = C.gates.take j.val ++ C.gates[j.val] :: C.gates.drop (j.val+1) := by simp
    conv_rhs => rw [splitC]
    simp only [List.filter_append,List.length_append,List.filter_cons]
    split <;> simp
  · intro x hx
    have notRead (t : Nat) (_ : j.val < t) (ht : t < C.gates.length) :
        N+j.val ∉ C.gates[t].inputs := by simpa [gateAt,ht] using hu t ht
    have eq := PruneWire.unread N C j.val N j.isLt notRead x hx C.output (Ne.symm hout)
    have outIndex : D.output = eraseRedirect N j.val N C.output := by simp [D,eraseGate,j.isLt]
    change (D.wires x).getD D.output false = (C.wires x).getD C.output false
    rw [outIndex]
    exact eq.symm

theorem prune511 {n : Nat} {G : Fin n → Fin n → Bool} (C : Circuit) (sh : shapes C)
    (back : ReadsBack (n+n) C) (rep : Represents G C) :
    ∃ D, shapes D ∧ ReadsBack (n+n) D ∧ Represents G D ∧ live (n+n) D ∧
      D.size ≤ C.size ∧ mixed (n+n) D ≤ mixed (n+n) C := by
  classical
  let good (s : Nat) := ∃ D : Circuit, shapes D ∧ ReadsBack (n+n) D ∧ Represents G D ∧
    mixed (n+n) D ≤ mixed (n+n) C ∧ D.size=s
  have witness : ∃ s, good s := ⟨C.size,C,sh,back,rep,le_rfl,rfl⟩
  obtain ⟨D,ds,db,dr,dm,sz⟩ := Nat.find_spec witness
  refine ⟨D,ds,db,dr,?_,?_,dm⟩
  · intro j hj
    by_contra! dead
    have hz : read D (n+n+j.val)=0 := by omega
    obtain ⟨es,eb,esz,em,ee⟩ := erase_dead ds db j hz hj
    let E := eraseGate (n+n) D j.val (n+n)
    have er : Represents G E := by
      intro u v
      exact (ee (oneEach u v) (by simp [oneEach])).trans (dr u v)
    have minimal := Nat.find_min' witness
      (show good E.size from ⟨E,es,eb,er,em.trans dm,rfl⟩)
    change E.size+1=D.size at esz
    omega
  · rw [sz]
    exact Nat.find_min' witness (show good C.size from ⟨C,sh,back,rep,le_rfl,rfl⟩)
end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds
lemma zeroCount511 {n : Nat} {C : Circuit}
    (row : ∀ u v : Fin n, read C u.val=0 → read C v.val=0 → u=v)
    (col : ∀ u v : Fin n, read C (n+u.val)=0 → read C (n+v.val)=0 → u=v) :
    ((Finset.range (n+n)).filter (fun w => read C w=0)).card ≤ 2 := by
  let s := (Finset.range (n+n)).filter (fun w => read C w=0)
  let low := s.filter (fun w => w<n)
  let high := s.filter (fun w => n≤w)
  have L : low.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨as,an⟩ := Finset.mem_filter.mp ha
    obtain ⟨bs,bn⟩ := Finset.mem_filter.mp hb
    exact congrArg Fin.val (row ⟨a,an⟩ ⟨b,bn⟩ (Finset.mem_filter.mp as).2 (Finset.mem_filter.mp bs).2)
  have H : high.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨as,an⟩ := Finset.mem_filter.mp ha
    obtain ⟨bs,bn⟩ := Finset.mem_filter.mp hb
    obtain ⟨ar,az⟩ := Finset.mem_filter.mp as
    obtain ⟨br,bz⟩ := Finset.mem_filter.mp bs
    have al := Finset.mem_range.mp ar
    have bl := Finset.mem_range.mp br
    have ea : n+(a-n)=a := by omega
    have eb : n+(b-n)=b := by omega
    have e := col ⟨a-n,by omega⟩ ⟨b-n,by omega⟩ (by simpa only [ea] using az) (by simpa only [eb] using bz)
    have h : a-n=b-n := congrArg Fin.val e
    omega
  have sub : s ⊆ low ∪ high := by
    intro a ha
    by_cases hl : a<n
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha,hl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha,by omega⟩)
  have x := Finset.card_le_card sub
  have y := Finset.card_union_le low high
  change s.card ≤ 2
  omega
end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def privateDouble (N : Nat) (C : Circuit) (g : Gate) : Prop :=
  ∃ a b : Nat, g.inputs = [a,b] ∧ a < N ∧ b < N ∧ read C a = 1 ∧ read C b = 1

def crossRaw {n : Nat} (C : Circuit) (g : Gate) (u v : Fin n) : Prop :=
  read C u.val = 1 ∧ read C (n+v.val) = 1 ∧
    (g.inputs = [u.val,n+v.val] ∨ g.inputs = [n+v.val,u.val])

theorem rawCountLE {C : Circuit} {j w : Nat} (hj : j < C.size) :
    (gateAt C j).inputs.count w ≤ read C w :=
  Finset.single_le_sum (f := fun i => (gateAt C i).inputs.count w)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)

theorem singleGate {C : Circuit} {i j w : Nat} (hi : i < C.size) (hj : j < C.size)
    (hw : read C w = 1) (hit : w ∈ (gateAt C i).inputs) (hjt : w ∈ (gateAt C j).inputs) :
    i = j := by
  by_contra neq
  have sub : ({i,j} : Finset Nat) ⊆ Finset.range C.size := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_range.mpr hi
    · simpa only [Finset.mem_singleton.mp hx] using Finset.mem_range.mpr hj
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => (gateAt C k).inputs.count w)
    sub (fun _ _ _ => Nat.zero_le _)
  simp only [Finset.sum_insert (by simpa using neq : i ∉ ({j} : Finset Nat)), Finset.sum_singleton] at h
  change (∑ a ∈ Finset.range C.size, (gateAt C a).inputs.count w) = 1 at hw
  have a := List.count_pos_iff.mpr hit
  have b := List.count_pos_iff.mpr hjt
  omega

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def singleSet (N : Nat) (C : Circuit) := (Finset.range N).filter (fun w => read C w = 1)
def manySet (N : Nat) (C : Circuit) := (Finset.range N).filter (fun w => 2 ≤ read C w)
def loads (s : Finset Nat) (g : Gate) := (g.inputs.filter (fun w => w ∈ s)).length

noncomputable def pairsOf (N : Nat) (C : Circuit) (o : GateOp) : Finset Nat := by
  classical
  exact (Finset.range C.size).filter (fun j => (gateAt C j).op=o ∧ privateDouble N C (gateAt C j))

private lemma listCounts (s : Finset Nat) (l : List Nat) :
    (∑ w ∈ s, l.count w) = (l.filter (fun w => w ∈ s)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, ih]
    by_cases mem : a ∈ s <;> simp [mem]

lemma totalLoads (s : Finset Nat) (C : Circuit) :
    (∑ j ∈ Finset.range C.size, loads s (gateAt C j)) = ∑ w ∈ s, read C w := by
  simp only [loads, ← listCounts, read, readsIn, Finset.sum_comm (s := Finset.range C.size) (t := s)]

private lemma listIndicators {α : Type} (l : List α) (d : α) (f : α → Bool) :
    (∑ j ∈ Finset.range l.length, if f (l.getD j d) then 1 else 0) = (l.filter f).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_zero, List.getD_cons_succ, ih]
    cases h : f a <;> simp [h]

private lemma slotsBound (N : Nat) (C : Circuit) (j : Nat) (hj : j < C.size) (sh : shapes C) :
    let g := gateAt C j
    loads (singleSet N C) g ≤ loads (manySet N C) g +
      (if g.inputs.length == 1 then 1 else 0) +
      (if g.inputs.length == 2 && (g.inputs.filter (fun w => w < N)).length == 1 then 1 else 0) +
      2*(if j ∈ pairsOf N C .and then 1 else 0) + 2*(if j ∈ pairsOf N C .or then 1 else 0) := by
  classical
  dsimp only
  let g := gateAt C j
  have mem : g ∈ C.gates := by
    simpa [g,gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using
      List.getElem_mem (l:=C.gates) (n:=j) hj
  have shape := sh g mem
  have pos (w : Nat) (h : w ∈ g.inputs) : 0 < read C w :=
    (List.count_pos_iff.mpr h).trans_le (rawCountLE hj)
  change loads (singleSet N C) g ≤ loads (manySet N C) g + _ + _ + _ + _
  have p (o : GateOp) : j ∈ pairsOf N C o ↔ g.op=o ∧ privateDouble N C g := by
    simp [pairsOf, hj, g]
  simp only [p]
  cases hs : g.inputs with
  | nil => simp [loads, hs]
  | cons a l =>
    cases l with
    | nil =>
      have ha : loads (singleSet N C) g ≤ 1 := by
        simpa [loads,hs] using List.length_filter_le (fun w => decide (w ∈ singleSet N C)) [a]
      simp [hs]
      omega
    | cons b l =>
      cases l with
      | cons c l => simp [hs] at shape
      | nil =>
        have ops : g.op=.and ∨ g.op=.or := by simpa [hs] using shape
        have a2 : 2 ≤ read C a ↔ read C a ≠ 1 := by have := pos a (by simp [hs]); omega
        have b2 : 2 ≤ read C b ↔ read C b ≠ 1 := by have := pos b (by simp [hs]); omega
        by_cases dp : privateDouble N C g
        · have cap : loads (singleSet N C) g ≤ 2 := by
            simpa [loads,hs] using List.length_filter_le (fun w => decide (w ∈ singleSet N C)) [a,b]
          rcases ops with op | op <;> simp [op, dp] <;> omega
        · have bad : ¬(a<N ∧ b<N ∧ read C a=1 ∧ read C b=1) :=
            fun h => dp ⟨a,b,hs,h⟩
          simp only [dp,and_false,ite_false,Nat.mul_zero,Nat.add_zero]
          by_cases ha : a<N <;> by_cases hb : b<N <;>
            by_cases ra : read C a=1 <;> by_cases rb : read C b=1 <;>
            simp [loads,hs,singleSet,manySet,ha,hb,a2,b2,ra,rb] at bad ⊢

lemma sumSlots (N : Nat) (C : Circuit) (sh : shapes C) :
    (∑ w ∈ singleSet N C, read C w) ≤ (∑ w ∈ manySet N C, read C w) +
      unary C + mixed N C + 2*(pairsOf N C .and).card + 2*(pairsOf N C .or).card := by
  classical
  have h := Finset.sum_le_sum (s:=Finset.range C.size) (fun j hj =>
    slotsBound N C j (Finset.mem_range.mp hj) sh)
  simp only [Finset.sum_add_distrib,totalLoads,← Finset.mul_sum,Finset.sum_boole,Nat.cast_id] at h
  have gateInd (f : Gate → Bool) :
      ((Finset.range C.size).filter (fun j => f (gateAt C j))).card = (C.gates.filter f).length := by
    have t := listIndicators C.gates ⟨.or,[]⟩ f
    simp only [Finset.sum_boole,Nat.cast_id] at t
    exact t
  have cardPair (o : GateOp) :
      ((Finset.range C.size).filter (· ∈ pairsOf N C o)).card = (pairsOf N C o).card := by
    congr 1
    apply Finset.filter_mem_eq_inter.trans
    exact Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  have u := gateInd (fun g => g.inputs.length == 1)
  have m := gateInd (fun g => g.inputs.length == 2 && (g.inputs.filter (fun w => w<N)).length == 1)
  rw [u,m,cardPair,cardPair] at h
  exact h

lemma wireWeights (N : Nat) (C : Circuit)
    (unread : ((Finset.range N).filter (fun w => read C w=0)).card ≤ 2) :
    N ≤ 2 + (∑ w ∈ singleSet N C, read C w) + excess N C ∧
    (∑ w ∈ manySet N C, read C w) ≤ 2*excess N C := by
  have first (w : Nat) : 1 ≤ (if read C w=0 then 1 else 0) +
      (if read C w=1 then read C w else 0) + (read C w-1) := by split <;> split <;> omega
  have second (w : Nat) : (if 2≤read C w then read C w else 0) ≤ 2*(read C w-1) := by
    split <;> omega
  have a := Finset.sum_le_sum (s:=Finset.range N) (fun w _ => first w)
  have b := Finset.sum_le_sum (s:=Finset.range N) (fun w _ => second w)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_boole,←Finset.sum_filter] at a
  rw [←Finset.sum_filter,←Finset.mul_sum] at b
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.mul_one,Nat.cast_id] at a
  exact ⟨by dsimp only [singleSet,excess]; omega,b⟩

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical

theorem coverMatch {n : Nat} (C : Circuit) (s : Finset Nat)
    (hs : ∀ j ∈ s, j<C.size ∧ (gateAt C j).op=.or ∧
        ∃ u v : Fin n, crossRaw C (gateAt C j) u v) :
    ∃ π : Equiv.Perm (Fin n), s.card ≤ (Finset.univ.filter (once C π)).card := by
  classical
  have pick (j : s) := (hs j.val j.property).2.2
  let row (j : s) := (pick j).choose
  let col (j : s) := (pick j).choose_spec.choose
  have pair (j : s) : crossRaw C (gateAt C j.val) (row j) (col j) := (pick j).choose_spec.choose_spec
  have mems (j : s) : (row j).val ∈ (gateAt C j.val).inputs ∧
      n+(col j).val ∈ (gateAt C j.val).inputs := by
    rcases (pair j).2.2 with h | h <;> simp [h]
  have ir : Function.Injective row := by
    intro i j eq
    apply Subtype.ext
    apply singleGate (hs _ i.property).1 (hs _ j.property).1 (pair i).1 (mems i).1
    simpa only [eq] using (mems j).1
  have ic : Function.Injective col := by
    intro i j eq
    apply Subtype.ext
    apply singleGate (hs _ i.property).1 (hs _ j.property).1 (pair i).2.1 (mems i).2
    simpa only [eq] using (mems j).2
  obtain ⟨π, extPair⟩ := Equiv.Perm.exists_extending_pair row col ir ic
  refine ⟨π, ?_⟩
  let good := Finset.univ.filter (once C π)
  have covered (j : s) : row j ∈ good := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold once
    rw [extPair]
    obtain ⟨hi,op,_⟩ := hs j.val j.property
    have m : gateAt C j.val ∈ C.gates := by
      simpa [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] using
        List.getElem_mem (l:=C.gates) (n:=j.val) hi
    exact ⟨(pair j).1,(pair j).2.1,gateAt C j.val,m,op,(pair j).2.2⟩
  let f (j : s) : good := ⟨row j,covered j⟩
  have fi : Function.Injective f := fun _ _ he => ir (congrArg Subtype.val he)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f fi

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical

theorem rawCoverage {n : Nat} (C : Circuit) (shape : shapes C)
    (unread : ((Finset.range (n+n)).filter (fun w => read C w=0)).card ≤ 2)
    (cross : ∀ j<C.size, privateDouble (n+n) C (gateAt C j) →
      ∃ u v : Fin n, crossRaw C (gateAt C j) u v)
    (onlyAnd : ∀ i<C.size, ∀ j<C.size, (gateAt C i).op=.and → (gateAt C j).op=.and →
      privateDouble (n+n) C (gateAt C i) → privateDouble (n+n) C (gateAt C j) → i=j) :
    ∃ π : Equiv.Perm (Fin n), 2*(n-(Finset.univ.filter (once C π)).card) ≤
      4+3*excess (n+n) C+unary C+mixed (n+n) C := by
  classical
  have inPair {j : Nat} {o : GateOp} (h : j ∈ pairsOf (n+n) C o) :
      j<C.size ∧ (gateAt C j).op=o ∧ privateDouble (n+n) C (gateAt C j) := by
    simpa only [pairsOf, Finset.mem_filter, Finset.mem_range] using h
  have one : (pairsOf (n+n) C .and).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨a, b, c⟩ := inPair hi
    obtain ⟨d, e, f⟩ := inPair hj
    exact onlyAnd i a j d b e c f
  obtain ⟨π, matchBound⟩ := coverMatch C (pairsOf (n+n) C .or) (fun j hj => by
    obtain ⟨a,b,c⟩ := inPair hj
    exact ⟨a,b,cross j a c⟩)
  have sums := sumSlots (n+n) C shape
  obtain ⟨wires,rep⟩ := wireWeights (n+n) C unread
  exact ⟨π, by omega⟩

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def lamp {n : Nat} (u c : Fin n) (w : Nat) := decide (w=u.val ∨ w=n+c.val)

private theorem rawVal {n : Nat} (C : Circuit) (u c : Fin n) {w : Nat} (hw : w<n+n) :
    Cross.val C (oneEach u c) w=lamp u c w := by
  apply Bool.eq_iff_iff.mpr
  rw [Cross.val_input (Cross.oe_len ..) hw,Cross.oe_getD]
  simp [lamp]

theorem privateTransfer {m : Nat} (hm : 5≤m) (C : Circuit) (back : ReadsBack (2*m+(2*m)) C)
    (rep : Represents (graph m) C) (u c v d : Fin (2*m)) (S : List Nat)
    (bare : ∀ s∈S,s<2*m+(2*m))
    (off : ∀ z, z<2*m+(2*m) → z∉S → lamp u c z=lamp v d z)
    (gates : ∀ j<C.size, (∃ w∈S,w∈(gateAt C j).inputs) →
      (∀ w∈(gateAt C j).inputs,w<2*m+(2*m)) ∧
      (gateAt C j).op.eval ((gateAt C j).inputs.map (lamp u c)) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (lamp v d))) :
    graph m u c=graph m v d := by
  let N := 2*m+(2*m)
  have byWire (w : Nat) (hn : w∉S) :
      Cross.val C (oneEach u c) w=Cross.val C (oneEach v d) w := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases lo : w<N
      · rw [rawVal C u c lo,rawVal C v d lo]
        exact off _ lo hn
      obtain ⟨j,rfl⟩ : ∃ j,w=N+j := ⟨w-N,by omega⟩
      by_cases hj : j<C.gates.length
      · rw [Cross.val_gate_rb (n:=N) (Cross.oe_len ..) hj (back j hj),
          Cross.val_gate_rb (n:=N) (Cross.oe_len ..) hj (back j hj)]
        by_cases hit : ∃ z∈S,z∈(gateAt C j).inputs
        · obtain ⟨low,e⟩ := gates j hj hit
          have M (a b : Fin (2*m)) : (gateAt C j).inputs.map (Cross.val C (oneEach a b)) =
              (gateAt C j).inputs.map (lamp a b) := by
            apply List.map_congr_left
            exact fun z hz => rawVal C a b (low z hz)
          simpa only [M] using e
        · congr 1
          apply List.map_congr_left
          exact fun z hz => ih z (back j hj z hz) (fun zs => hit ⟨z,zs,hz⟩)
      · rw [Cross.val_ge (n:=N) (Cross.oe_len ..) (by omega),Cross.val_ge (n:=N) (Cross.oe_len ..) (by omega)]
  have hi := internalOutput hm C rep
  have e := byWire C.output (fun o => by have := bare _ o;omega)
  exact (rep u c).symm.trans (e.trans (rep v d))

private theorem mapSwap {n : Nat} {C : Circuit} {i : Nat} {p q : Nat} {u c v d : Fin n}
    (op : (gateAt C i).op=.and ∨ (gateAt C i).op=.or)
    (shape : (gateAt C i).inputs=[p,q] ∨ (gateAt C i).inputs=[q,p])
    (s1 : lamp u c p=lamp v d q) (s2 : lamp u c q=lamp v d p) :
    (gateAt C i).op.eval ((gateAt C i).inputs.map (lamp u c)) =
      (gateAt C i).op.eval ((gateAt C i).inputs.map (lamp v d)) := by
  rcases op with op|op <;> rcases shape with h|h <;>
    simp [op,h,GateOp.eval,s1,s2,Bool.and_comm,Bool.or_comm]

theorem swapPair {m : Nat} (hm : 5≤m) (C : Circuit) (back : ReadsBack (2*m+(2*m)) C)
    (rep : Represents (graph m) C) {p q : Nat} (hp : p<2*m+(2*m)) (hq : q<2*m+(2*m))
    {j : Nat} (hj : j<C.size) (rp : read C p=1) (rq : read C q=1)
    (op : (gateAt C j).op=.and ∨ (gateAt C j).op=.or)
    (shape : (gateAt C j).inputs=[p,q] ∨ (gateAt C j).inputs=[q,p])
    (u c v d : Fin (2*m)) (s1 : lamp u c p=lamp v d q) (s2 : lamp u c q=lamp v d p)
    (off : ∀ z, z≠p → z≠q → lamp u c z=lamp v d z) : graph m u c=graph m v d := by
  apply privateTransfer hm C back rep u c v d [p,q]
  · intro s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl <;> assumption
  · intro z _ hz
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hz
    exact off z hz.1 hz.2
  · intro t ht hit
    obtain ⟨z,hz,inG⟩ := hit
    have mem : p ∈ (gateAt C j).inputs ∧ q ∈ (gateAt C j).inputs := by rcases shape with h|h <;> simp [h]
    have tj : t=j := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl
      · exact singleGate ht hj rp inG mem.1
      · exact singleGate ht hj rq inG mem.2
    subst t
    refine ⟨?_,mapSwap op shape s1 s2⟩
    intro w hw
    rcases shape with h|h <;> simp only [h,List.mem_cons,List.not_mem_nil,or_false] at hw <;> omega

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux

private lemma wrapSmall {m x : Nat} (hm : 0<m) (hx : x<2*m) : x%m=x ∨ x%m+m=x := by
  by_cases small : x<m
  · exact Or.inl (Nat.mod_eq_of_lt small)
  · right
    rw [Nat.mod_eq_sub_mod (by omega : m ≤ x),Nat.mod_eq_of_lt (by omega : x-m<m)]
    omega

private lemma evenEdge {m : Nat} (u : Fin (2*m)) (j : Fin m) :
    graph m u (Rows.point j false)=true ↔ u.val/2=j.val ∨ u.val/2=(j.val+1)%m := by
  simp [graph,Rows.pointGroup,Rows.pointSide]

private lemma oddEdge {m : Nat} (u : Fin (2*m)) (j : Fin m) :
    graph m u (Rows.point j true)=true ↔ u.val/2=j.val ∨ u.val/2=(j.val+(2+u.val %2))%m := by
  simp [graph,Rows.pointGroup,Rows.pointSide]

theorem rowsUnique {m : Nat} (hm : 5≤m) {u v : Fin (2*m)}
    (same : ∀ c, graph m u c=graph m v c) : u=v := by
  let a := Rows.group u
  let b := Rows.group v
  have ha : (a:Nat)=u.val/2 := rfl
  have hb : (b:Nat)=v.val/2 := rfl
  have ea : graph m v (Rows.point a false)=true := (same _).symm.trans ((evenEdge u a).2 (Or.inl ha.symm))
  have eb : graph m u (Rows.point b false)=true := (same _).trans ((evenEdge v b).2 (Or.inl hb.symm))
  have IJ := (evenEdge v a).1 ea
  have JI := (evenEdge u b).1 eb
  have al := a.isLt
  have bl := b.isLt
  have groupEq : u.val/2 = v.val/2 := by
    have wa := wrapSmall (by omega : 0<m) (show a.val+1<2*m by omega)
    have wb := wrapSmall (by omega : 0<m) (show b.val+1<2*m by omega)
    omega
  let d := 2+u.val %2
  let d' := 2+v.val %2
  let j := Rows.prev a d
  have jd : j.val=(a.val+m-d)%m := rfl
  have jl := j.isLt
  have d1 : 2≤d ∧ d≤3 := by dsimp [d];omega
  have d2 : 2≤d' ∧ d'≤3 := by dsimp [d'];omega
  have wa := wrapSmall (by omega : 0<m) (show a.val+m-d<2*m by omega)
  have wj := wrapSmall (by omega : 0<m) (show j.val+d<2*m by omega)
  have wj' := wrapSmall (by omega : 0<m) (show j.val+d'<2*m by omega)
  have hmq : (j.val+d)%m<m := Nat.mod_lt _ (by omega)
  have neigh : graph m u (Rows.point j true)=true := (oddEdge u j).2 (Or.inr (by change u.val/2=(j.val+d)%m;omega))
  have other := (oddEdge v j).1 ((same _).symm.trans neigh)
  change v.val/2=j.val ∨ v.val/2=(j.val+d')%m at other
  have parity : d=d' := by omega
  dsimp [d,d'] at parity
  apply Fin.ext
  omega

theorem colsUnique {m : Nat} (hm : 5≤m) {v w : Fin (2*m)}
    (same : ∀ a, graph m a v=graph m a w) : v=w := by
  by_contra ne
  obtain ⟨a,b,_,av,aw,_⟩ := Col.colMiss hm v w ne
  have e := av.symm.trans ((same a).trans aw)
  contradiction

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private lemma lampRow {n : Nat} (u c p : Fin n) : lamp u c p.val=decide (p=u) := by
  have low : p.val ≠ n+c.val := by have := p.isLt;omega
  simp [lamp,low,Fin.ext_iff]

private lemma lampCol {n : Nat} (u c p : Fin n) : lamp u c (n+p.val)=decide (p=c) := by
  have high : n+p.val ≠ u.val := by have := u.isLt;omega
  simp [lamp,high,Fin.ext_iff]

theorem rowPairNo {m : Nat} (hm : 5≤m) (C : Circuit) (back : ReadsBack (2*m+(2*m)) C)
    (rep : Represents (graph m) C) {i : Nat} (hi : i<C.size) {u v : Fin (2*m)} (ne : u≠v)
    (ru : read C u.val=1) (rv : read C v.val=1)
    (op : (gateAt C i).op=.and ∨ (gateAt C i).op=.or)
    (shape : (gateAt C i).inputs=[u.val,v.val] ∨ (gateAt C i).inputs=[v.val,u.val]) : False := by
  apply ne
  apply rowsUnique hm
  intro c
  apply swapPair hm C back rep (by have := u.isLt;omega) (by have := v.isLt;omega) hi ru rv op shape u c v c
  · simp [lampRow]
  · simp [lampRow,eq_comm]
  · intro z zu zv
    simp [lamp,zu,zv]

theorem colPairNo {m : Nat} (hm : 5≤m) (C : Circuit) (back : ReadsBack (2*m+(2*m)) C)
    (rep : Represents (graph m) C) {i : Nat} (hi : i<C.size) {u v : Fin (2*m)} (ne : u≠v)
    (ru : read C (2*m+u.val)=1) (rv : read C (2*m+v.val)=1)
    (op : (gateAt C i).op=.and ∨ (gateAt C i).op=.or)
    (shape : (gateAt C i).inputs=[2*m+u.val,2*m+v.val] ∨ (gateAt C i).inputs=[2*m+v.val,2*m+u.val]) : False := by
  apply ne
  apply colsUnique hm
  intro a
  apply swapPair hm C back rep (by have := u.isLt;omega) (by have := v.isLt;omega) hi ru rv op shape a u a v
  · simp [lampCol]
  · simp [lampCol,eq_comm]
  · intro z zu zv
    simp [lamp,zu,zv]

private theorem zeroTransfer {m : Nat} (hm : 5≤m) (C : Circuit) (back : ReadsBack (2*m+(2*m)) C)
    (rep : Represents (graph m) C) (u c v d : Fin (2*m)) {p q : Nat}
    (hp : p<2*m+(2*m)) (hq : q<2*m+(2*m)) (rp : read C p=0) (rq : read C q=0)
    (off : ∀ z, z≠p → z≠q → lamp u c z=lamp v d z) : graph m u c=graph m v d := by
  apply privateTransfer hm C back rep u c v d [p,q]
  · intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    omega
  · intro z _ hz
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hz
    exact off z hz.1 hz.2
  · intro j hj h
    obtain ⟨s,hs,si⟩ := h
    have pos := List.count_pos_iff.mpr si
    have le := rawCountLE (w:=s) hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl <;> omega

theorem zeroRowUnique {m : Nat} (hm : 5≤m) (C : Circuit) (back : ReadsBack (2*m+(2*m)) C)
    (rep : Represents (graph m) C) {u v : Fin (2*m)}
    (ru : read C u.val=0) (rv : read C v.val=0) : u=v := by
  apply rowsUnique hm
  intro c
  apply zeroTransfer hm C back rep u c v c (by have := u.isLt;omega) (by have := v.isLt;omega) ru rv
  intro z zu zv
  simp [lamp,zu,zv]

theorem zeroColUnique {m : Nat} (hm : 5≤m) (C : Circuit) (back : ReadsBack (2*m+(2*m)) C)
    (rep : Represents (graph m) C) {u v : Fin (2*m)}
    (ru : read C (2*m+u.val)=0) (rv : read C (2*m+v.val)=0) : u=v := by
  apply colsUnique hm
  intro a
  apply zeroTransfer hm C back rep a u a v (by have := u.isLt;omega) (by have := v.isLt;omega) ru rv
  intro z zu zv
  simp [lamp,zu,zv]

private theorem andColumns {m : Nat} (hm : 5≤m) (C : Circuit) (back : ReadsBack (2*m+(2*m)) C)
    (rep : Represents (graph m) C) {a u v b c : Fin (2*m)} (au : a≠u) (av : a≠v)
    {j t : Nat} (hj : j<C.size) (ht : t<C.size) (opj : (gateAt C j).op=.and) (opt : (gateAt C t).op=.and)
    (shj : crossRaw C (gateAt C j) u b) (sht : crossRaw C (gateAt C t) v c) :
    graph m a b=graph m a c := by
  let n := 2*m
  apply privateTransfer hm C back rep a b a c [n+b.val,n+c.val]
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    have := b.isLt
    have := c.isLt
    dsimp [n] at hz
    omega
  · intro z _ hz
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hz
    simp [lamp,show z≠2*m+b.val from hz.1,show z≠2*m+c.val from hz.2]
  · intro i hi hit
    have killed (j : Nat) (u v : Fin (2*m)) (au : a≠u) (opj : (gateAt C j).op=.and)
        (shape : crossRaw C (gateAt C j) u v) :
        (∀ z∈(gateAt C j).inputs,z<2*m+(2*m)) ∧
        (gateAt C j).op.eval ((gateAt C j).inputs.map (lamp a b)) =
          (gateAt C j).op.eval ((gateAt C j).inputs.map (lamp a c)) := by
      obtain ⟨_,_,s|s⟩ := shape <;> constructor
      all_goals first
        | (intro z hz; simp only [s,List.mem_cons,List.not_mem_nil,or_false] at hz;
           have := u.isLt; have := v.isLt; omega)
        | (simp [opj,s,GateOp.eval,lampRow,Ne.symm au])
    obtain ⟨s,hs,inp⟩ := hit
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl
    · have mem : n+b.val ∈ (gateAt C j).inputs := by rcases shj.2.2 with s|s <;> simp [s,n]
      have ij := singleGate hi hj shj.2.1 inp mem
      subst i
      exact killed j u b au opj shj
    · have mem : n+c.val ∈ (gateAt C t).inputs := by rcases sht.2.2 with s|s <;> simp [s,n]
      have it := singleGate hi ht sht.2.1 inp mem
      subst i
      exact killed t v c av opt sht

theorem andPairNo {m : Nat} (hm : 5≤m) (C : Circuit) (back : ReadsBack (2*m+(2*m)) C)
    (rep : Represents (graph m) C) {u v b c : Fin (2*m)}
    {j t : Nat} (hj : j<C.size) (ht : t<C.size) (opj : (gateAt C j).op=.and) (opt : (gateAt C t).op=.and)
    (shj : crossRaw C (gateAt C j) u b) (sht : crossRaw C (gateAt C t) v c) : j=t := by
  by_cases e : b=c
  · subst c
    apply singleGate hj ht shj.2.1
    · rcases shj.2.2 with h|h <;> simp [h]
    · rcases sht.2.2 with h|h <;> simp [h]
  · have bound := colFar hm b c e
    have sub : Finset.univ.filter (fun a : Fin (2*m) => graph m a b≠graph m a c) ⊆ {u,v} := by
      intro a ha
      by_contra outside
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at outside
      exact (Finset.mem_filter.mp ha).2 (andColumns hm C back rep outside.1 outside.2 hj ht opj opt shj sht)
    have le := Finset.card_le_card sub
    have h := Finset.card_insert_le u ({v} : Finset _)
    rw [Finset.card_singleton] at h
    omega

end PEqualNP.Outside.L_meta_25511_aux

namespace PEqualNP.Outside.L_meta_25511_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

theorem crossShape {m : Nat} (hm : 5≤m) (C : Circuit) (sh : shapes C)
    (back : ReadsBack (2*m+(2*m)) C) (rep : Represents (graph m) C)
    (j : Nat) (hj : j<C.size) (priv : privateDouble (2*m+(2*m)) C (gateAt C j)) :
    ∃ u v : Fin (2*m), crossRaw C (gateAt C j) u v := by
  let n := 2*m
  obtain ⟨a,b,shape,ha,hb,ra,rb⟩ := priv
  have ao : (gateAt C j).op=.and ∨ (gateAt C j).op=.or := by
    rcases sh _ (Cross.gateAt_mem hj) with ⟨h,_⟩|⟨_,l⟩
    · exact h
    · simp [shape] at l
  have distinct : a≠b := by
    rintro rfl
    have le := rawCountLE (w:=a) hj
    rw [shape,ra] at le
    simp at le
  by_cases ar : a<n
  · let u : Fin n := ⟨a,ar⟩
    by_cases br : b<n
    · let v : Fin n := ⟨b,br⟩
      exact False.elim (rowPairNo hm C back rep hj (u:=u) (v:=v) (fun e => distinct (congrArg Fin.val e))
        ra rb ao (Or.inl shape))
    · let v : Fin n := ⟨b-n,by dsimp [n] at *;omega⟩
      have e : n+v.val=b := by dsimp [v];omega
      refine ⟨u,v,ra,?_,Or.inl ?_⟩
      · change read C (n+v.val)=1
        rwa [e]
      · change (gateAt C j).inputs=[a,n+v.val]
        rwa [e]
  · let u : Fin n := ⟨a-n,by dsimp [n] at *;omega⟩
    have e : n+u.val=a := by dsimp [u];omega
    by_cases br : b<n
    · let v : Fin n := ⟨b,br⟩
      refine ⟨v,u,rb,?_,Or.inr ?_⟩
      · change read C (n+u.val)=1
        rwa [e]
      · change (gateAt C j).inputs=[n+u.val,b]
        rwa [e]
    · let v : Fin n := ⟨b-n,by dsimp [n] at *;omega⟩
      have f : n+v.val=b := by dsimp [v];omega
      have ne : u≠v := by
        intro same
        have := congrArg Fin.val same
        omega
      apply False.elim
      apply colPairNo hm C back rep hj (u:=u) (v:=v) ne _ _ ao
      · change _=[n+u.val,n+v.val] ∨ _=[n+v.val,n+u.val]
        rw [e,f]
        exact Or.inl shape
      · change read C (n+u.val)=1
        rwa [e]
      · change read C (n+v.val)=1
        rwa [f]

theorem singleAnd {m : Nat} (hm : 5≤m) (C : Circuit) (sh : shapes C)
    (back : ReadsBack (2*m+(2*m)) C) (rep : Represents (graph m) C)
    (i : Nat) (hi : i<C.size) (j : Nat) (hj : j<C.size) (oi : (gateAt C i).op=.and)
    (oj : (gateAt C j).op=.and) (pi : privateDouble (2*m+(2*m)) C (gateAt C i))
    (pj : privateDouble (2*m+(2*m)) C (gateAt C j)) : i=j := by
  obtain ⟨u,b,h⟩ := crossShape hm C sh back rep i hi pi
  obtain ⟨v,c,h'⟩ := crossShape hm C sh back rep j hj pj
  exact andPairNo hm C back rep hi hj oi oj h h'

end PEqualNP.Outside.L_meta_25511_aux

open PEqualNP.Outside.L_meta_25511_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25511 :
∀ (m : ℕ), 5 ≤ m →
  let n := 2 * m
  let G := fun (u v : Fin n) =>
    let i := u.val / 2
    let j := v.val / 2
    let offset := if v.val % 2 = 0 then 1 else 2 + u.val % 2
    decide (i = j ∨ i = (j + offset) % m)
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    let mixed := (C.gates.filter (fun gate =>
      gate.inputs.length == 2 &&
      (gate.inputs.filter (fun w => w < n + n)).length == 1)).length
    (∀ g ∈ C.gates,
      ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + n) C →
    PEqualNP.Represents.Represents G C →
    38 * m ≤ 9 * C.size + 3 * mixed + 39 := by
  intro m hm n G C M shape rb rep
  classical
  change shapes C at shape
  change Represents (graph m) C at rep
  obtain ⟨D,sh,back,dr,hl,hs,hM⟩ := prune511 C shape rb rep
  have zero := zeroCount511 (n:=n) (C:=D)
    (fun u v => zeroRowUnique hm D back dr (u:=u) (v:=v))
    (fun u v => zeroColUnique hm D back dr (u:=u) (v:=v))
  have matched := rawCoverage (n:=n) D sh zero (crossShape hm D sh back dr) (singleAnd hm D sh back dr)
  have value := price511 hm D sh back dr hl zero matched
  change 38*m ≤ 9*C.size+3*mixed (n+n) C+39
  change mixed (2*m+2*m) D ≤ mixed (2*m+2*m) C at hM
  dsimp [n]
  omega
