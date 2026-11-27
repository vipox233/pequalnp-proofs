import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25465.Chriesistei

-- Fold, cone and restriction lemmas adapted from public L_meta_24698 by Maxime Moisant.

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


open PEqualNP.Represents PEqualNP.EdgeOwnership

-- oneEach input calculation from public L_meta_25021 by odinfree.
theorem oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt; have hv := v.isLt
  unfold oneEach
  by_cases h1 : i < n
  · rw [List.getD_append _ _ _ _ (by simp [h1])]
    simp [List.getD_eq_getElem?_getD, h1, Fin.ext_iff]
    omega
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    by_cases h2 : i < n + m
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, show i - n < m by omega,
        ↓reduceDIte, Option.getD_some, Fin.ext_iff, decide_eq_decide]
      omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp only [false_eq_decide_iff]; omega

abbrev RO (C : Circuit) :=
  ∀ w : ℕ, ((List.range C.gates.length).map fun r => (gateAt C r).inputs.count w).sum ≤ 1

abbrev Reach (N : ℕ) (C : Circuit) := Relation.ReflTransGen (coneRd N C)

theorem sum_range_list (f : ℕ → ℕ) (k : ℕ) :
    ((List.range k).map f).sum = ∑ j ∈ Finset.range k, f j := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem edge_unique {N : ℕ} {C : Circuit} (h : RO C) : Relator.RightUnique (coneRd N C) := by
  rintro w a b ⟨ha, ha', hwa⟩ ⟨hb, hb', hwb⟩
  by_contra hne
  have hj : a - N ≠ b - N := by omega
  let f := fun j => (gateAt C j).inputs.count w
  have hsub : ({a-N,b-N} : Finset ℕ) ⊆ Finset.range C.gates.length := by
    intro j hj'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj'
    rw [Finset.mem_range]; omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := f) hsub (fun _ _ _ => Nat.zero_le _)
  simp [hj] at hle
  have hA : 0 < f (a-N) := List.count_pos_iff.mpr hwa
  have hB : 0 < f (b-N) := List.count_pos_iff.mpr hwb
  have htotal : (∑ j ∈ Finset.range C.gates.length, f j) ≤ 1 := by
    rw [← sum_range_list]; exact h w
  omega

def tab (k : ℕ) (f : ℕ → Gate) (o : ℕ) : Circuit :=
  ⟨List.ofFn (fun i : Fin k => f i.val), o⟩

@[simp] theorem tab_len (k f o) : (tab k f o).gates.length = k := by simp [tab]

theorem tab_at (k f o) {j : ℕ} (hj : j < k) : gateAt (tab k f o) j = f j := by
  have hl : j < (tab k f o).gates.length := by simpa using hj
  rw [gateAt_eq hl]; simp [tab]

def constG (a : Bool) : Gate := ⟨if a then .and else .or, []⟩

@[simp] theorem constG_eval (a : Bool) : (constG a).op.eval [] = a := by cases a <;> rfl

@[simp] theorem constG_inputs (a : Bool) : (constG a).inputs = [] := rfl

def cutG (C : Circuit) (p q : ℕ) (a b : Bool) (j : ℕ) : Gate :=
  if j = p then constG a else if j = q then constG b else gateAt C j

def cut (C : Circuit) (p q : ℕ) (a b : Bool) : Circuit :=
  tab C.gates.length (cutG C p q a b) C.output

@[simp] theorem cut_len (C p q a b) : (cut C p q a b).gates.length = C.gates.length := by simp [cut]

theorem cut_at (C p q a b) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (cut C p q a b) j = cutG C p q a b j := tab_at _ _ _ hj

theorem cut_inputs {C p q a b j w} (hj : j < C.gates.length)
    (h : w ∈ (gateAt (cut C p q a b) j).inputs) :
    j ≠ p ∧ j ≠ q ∧ w ∈ (gateAt C j).inputs := by
  rw [cut_at _ _ _ _ _ hj] at h
  by_cases hp : j = p <;> by_cases hq : j = q <;> simp_all [cutG, constG]

theorem cut_rb {N C p q a b} (hr : ReadsBack N C) : ReadsBack N (cut C p q a b) := by
  intro j hj w hw
  rw [cut_len] at hj
  exact hr j hj w (cut_inputs hj hw).2.2

theorem cut_step {N C p q a b z w} (he : coneRd N (cut C p q a b) z w) :
    coneRd N C z w ∧ w ≠ N+p ∧ w ≠ N+q := by
  obtain ⟨h1,h2,h3⟩ := he
  rw [cut_len] at h2
  obtain ⟨hp,hq,h⟩ := cut_inputs (by omega) h3
  exact ⟨⟨h1,h2,h⟩, by omega, by omega⟩

theorem blocked_path {N C p q a b w t o} (hr : ReadsBack N C) (hro : RO C)
    (ht : t = N+p ∨ t = N+q) (hw : w ≠ t) (hwt : Reach N C w t)
    (hcut : Reach N (cut C p q a b) w o) : o < t := by
  have aux : Reach N C o t ∧ o ≠ t := by
    induction hcut with
    | refl => exact ⟨hwt, hw⟩
    | tail _ step ih =>
      obtain ⟨he,hp,hq⟩ := cut_step step
      rcases ih.1.cases_head with h | ⟨v,hv,hvt⟩
      · exact (ih.2 h).elim
      · obtain rfl := edge_unique (N := N) hro hv he
        exact ⟨hvt, by rcases ht with rfl|rfl <;> assumption⟩
  have hle := coneRtg_le hr aux.1
  exact lt_of_le_of_ne hle aux.2

theorem reaches_from_body {N C k w} (hr : ReadsBack N C) (hk : k < C.gates.length)
    (hw : w < N) (h : ∃ i, (i = k ∨ InCone N C i k) ∧ w ∈ (gateAt C i).inputs) :
    Reach N C w (N+k) := by
  apply (coneRd_reach_iff hr hk w (by omega)).2
  obtain ⟨i,hi,hin⟩ := h
  exact ⟨i,(mem_coneSet N C i k).2 hi,hin⟩

theorem root_no_path {N C p q h h'} (hr : ReadsBack N C) (ro : RO C)
    (sp : coneRd N C (N+h) (N+p)) (sq : coneRd N C (N+h') (N+q))
    (hpq : p ≠ q) (hinc : ¬(p = h' ∨ InCone N C p h')) :
    ¬ Reach N C (N+h) (N+h') := by
  intro hpath
  rcases hpath.cases_head with he | ⟨v,hv,hvt⟩
  · rw [he] at sp
    have := edge_unique ro sp sq
    omega
  · have he := edge_unique ro hv sp
    subst v
    by_cases heq : p = h'
    · exact hinc (Or.inl heq)
    · apply hinc ∘ Or.inr
      simpa using coneRtg_inCone hr (N+p) (N+h') hvt (by omega) (by omega)

theorem cones_exclusive {N C p q h h' w} (hr : ReadsBack N C) (ro : RO C)
    (sp : coneRd N C (N+h) (N+p)) (sq : coneRd N C (N+h') (N+q))
    (hpq : p ≠ q) (hp : ¬(p = h' ∨ InCone N C p h'))
    (hq : ¬(q = h ∨ InCone N C q h)) (hw : Reach N C w (N+h)) :
    ¬ Reach N C w (N+h') := by
  intro hw'
  rcases Relation.ReflTransGen.total_of_right_unique (edge_unique ro) hw hw' with path|path
  · exact root_no_path hr ro sp sq hpq hp path
  · exact root_no_path hr ro sq sp hpq.symm hq path

theorem val_local {N C x y} (rb : ReadsBack N C) (hx : List.length x = N)
    (hy : List.length y = N) (o : ℕ) :
    (∀ w < N, Reach N C w o → x.getD w false = y.getD w false) →
    val C x o = val C y o := by
  induction o using Nat.strong_induction_on with
  | _ o ih =>
    intro H
    by_cases h0 : o < N
    · simpa only [val_input hx h0, val_input hy h0] using H o h0 .refl
    obtain ⟨j, rfl⟩ : ∃ j, o = N+j := ⟨o-N, by omega⟩
    by_cases hj : j < C.gates.length
    · rw [val_gate_rb hx hj (rb j hj), val_gate_rb hy hj (rb j hj)]
      congr 1
      apply List.map_congr_left
      intro i hi
      apply ih i (rb j hj i hi)
      intro w hw hr
      exact H w hw (hr.tail (coneRd_of_input hj hi))
    · rw [val_ge hx (by omega), val_ge hy (by omega)]

def zeros (N : ℕ) := List.replicate N false

theorem cut_zero_of_active {n m C p q a b t o} {u : Fin n} {v : Fin m}
    (hr : ReadsBack (n+m) C) (hro : RO C)
    (ht : t = n+m+p ∨ t = n+m+q) (hto : t ≤ o)
    (hu : Reach (n+m) C u.val t) (hv : Reach (n+m) C (n+v.val) t) :
    val (cut C p q a b) (oneEach u v) o = val (cut C p q a b) (zeros (n+m)) o := by
  apply val_local (cut_rb hr) (oneEach_len u v) (by simp [zeros]) o
  intro w hw hreach
  have hu' := u.isLt
  have hv' := v.isLt
  have hwu : w ≠ u.val := by
    rintro rfl
    have := blocked_path hr hro ht (by rcases ht with rfl|rfl <;> omega) hu hreach
    omega
  have hwv : w ≠ n+v.val := by
    rintro rfl
    have := blocked_path hr hro ht (by rcases ht with rfl|rfl <;> omega) hv hreach
    omega
  rw [oneEach_getD]
  simp [hwu, hwv, zeros, List.getD_eq_getElem?_getD, hw]

theorem cut_val_source {N C p q a b x} (hr : ReadsBack N C) (hx : List.length x = N)
    (hA : a = val C x (N+p)) (hB : b = val C x (N+q)) (o : ℕ) :
    val (cut C p q a b) x o = val C x o := by
  induction o using Nat.strong_induction_on with
  | _ o ih =>
    by_cases h0 : o < N
    · rw [val_input hx h0, val_input hx h0]
    obtain ⟨j,rfl⟩ : ∃ j, o = N+j := ⟨o-N, by omega⟩
    by_cases hj : j < C.gates.length
    · have hj' : j < (cut C p q a b).gates.length := by simpa using hj
      rw [val_gate_rb hx hj' (cut_rb hr j hj'), cut_at _ _ _ _ _ hj]
      by_cases hp : j = p
      · subst j; simpa [cutG] using hA
      by_cases hq : j = q
      · subst j; simpa [cutG, hp] using hB
      rw [show cutG C p q a b j = gateAt C j by simp [cutG, hp, hq],
        val_gate_rb hx hj (hr j hj)]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih i (hr j hj i hi)
    · rw [val_ge hx (by simp; omega), val_ge hx (by omega)]

theorem mono_gate {op : GateOp} (hop : op = .and ∨ op = .or) (l : List ℕ)
    {f g : ℕ → Bool} (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl|rfl
  · simp only [eval_and_iff]
    exact fun h' i hi => h i hi (h' i hi)
  · simp only [eval_or_iff]
    rintro ⟨i,hi,hf⟩
    exact ⟨i,hi,h i hi hf⟩

abbrev MonoRest (C : Circuit) (p q : ℕ) :=
  ∀ j < C.gates.length, j ≠ p → j ≠ q → (gateAt C j).op = .and ∨ (gateAt C j).op = .or

theorem cut_val_mono {N C p q a b a' b' x y} (hr : ReadsBack N C) (mono : MonoRest C p q)
    (hx : List.length x = N) (hy : List.length y = N) (hab : a = true → a' = true)
    (hbb : b = true → b' = true) (hxy : ∀ w < N, x.getD w false = true → y.getD w false = true)
    (o : ℕ) : val (cut C p q a b) x o = true → val (cut C p q a' b') y o = true := by
  induction o using Nat.strong_induction_on with
  | _ o ih =>
    by_cases h0 : o < N
    · simpa only [val_input hx h0, val_input hy h0] using hxy o h0
    obtain ⟨j,rfl⟩ : ∃ j, o = N+j := ⟨o-N, by omega⟩
    by_cases hj : j < C.gates.length
    · have h1 : j < (cut C p q a b).gates.length := by simpa using hj
      have h2 : j < (cut C p q a' b').gates.length := by simpa using hj
      rw [val_gate_rb hx h1 (cut_rb hr j h1), val_gate_rb hy h2 (cut_rb hr j h2),
        cut_at _ _ _ _ _ hj, cut_at _ _ _ _ _ hj]
      by_cases hp : j = p
      · simpa [cutG, hp] using hab
      by_cases hq : j = q
      · subst j; simpa [cutG, hp] using hbb
      simp only [cutG, if_neg hp, if_neg hq]
      apply mono_gate (mono j hj hp hq)
      intro i hi
      exact ih i (hr j hj i hi)
    · rw [val_ge (u := N+j) (C := cut C p q a b) hx (by rw [cut_len]; omega)]
      simp

theorem scalar_collapse (u v g c0 c1 c2 f : Bool)
    (hex : u = true → v = false)
    (h0 : u = false → v = false → f = g)
    (h1 : u = true → f = c1 ∧ g = c0)
    (h2 : v = true → f = c2 ∧ g = c0)
    (hG : c0 = true → g = true) (hC1 : c1 = true → c0 = true)
    (hC2 : c2 = true → c0 = true) :
    f = (if c0 then !((u && !c1) || (v && !c2)) else g) := by
  cases u <;> cases v <;> cases c0 <;> cases c1 <;> cases c2 <;> simp_all

structure Body (n m : ℕ) (C : Circuit) (p h : ℕ) : Prop where
  idx : p < C.gates.length
  op : (gateAt C p).op = .not
  head : (gateAt C p).inputs.head? = some (n+m+h)
  lt : h < p
  cross : ∀ (u : Fin n) (v : Fin m), val C (oneEach u v) (n+m+h) = true →
    (∃ i, (i = h ∨ InCone (n+m) C i h) ∧ u.val ∈ (gateAt C i).inputs) ∧
    (∃ i, (i = h ∨ InCone (n+m) C i h) ∧ n+v.val ∈ (gateAt C i).inputs)

theorem head_cons' {l : List ℕ} {w} (he : l.head? = some w) : ∃ tail, l = w :: tail := by
  cases l <;> simp_all

theorem Body.edge {n m C p h} (b : Body n m C p h) : coneRd (n+m) C (n+m+h) (n+m+p) := by
  obtain ⟨l,he⟩ := head_cons' b.head
  exact coneRd_of_input b.idx (by rw [he]; simp)

theorem Body.neg {n m C p h} (b : Body n m C p h) (hr : ReadsBack (n+m) C)
    {x : List Bool} (hx : x.length = n+m) :
    val C x (n+m+p) = !(val C x (n+m+h)) := by
  obtain ⟨l,he⟩ := head_cons' b.head
  rw [val_gate_rb hx b.idx (hr p b.idx), b.op, he]
  rfl

theorem Body.lit {n m C p h} (b : Body n m C p h) (hr : ReadsBack (n+m) C)
    (u : Fin n) (v : Fin m) (hv : val C (oneEach u v) (n+m+h) = true) :
    Reach (n+m) C u.val (n+m+h) ∧ Reach (n+m) C (n+v.val) (n+m+h) := by
  obtain ⟨hu,hv'⟩ := b.cross u v hv
  have hlt : h < C.gates.length := lt_trans b.lt b.idx
  have := u.isLt
  have := v.isLt
  exact ⟨reaches_from_body hr hlt (by omega) hu, reaches_from_body hr hlt (by omega) hv'⟩

def zeroCof (N : ℕ) (C : Circuit) (p q o : ℕ) (a b : Bool) :=
  val (cut C p q a b) (zeros N) o

theorem cofactor {n m C p q h h' o} (hp : Body n m C p h) (hq : Body n m C q h')
    (rb : ReadsBack (n+m) C) (ro : RO C) (mono : MonoRest C p q) (hne : p ≠ q)
    (ip : ¬(p = h' ∨ InCone (n+m) C p h')) (iq : ¬(q = h ∨ InCone (n+m) C q h))
    (ho1 : n+m+p ≤ o) (ho2 : n+m+q ≤ o) (u : Fin n) (v : Fin m) :
    val C (oneEach u v) o =
    (if zeroCof (n+m) C p q o true true then
      !((val C (oneEach u v) (n+m+h) && !(zeroCof (n+m) C p q o false true)) ||
        (val C (oneEach u v) (n+m+h') && !(zeroCof (n+m) C p q o true false)))
     else val (cut C p q true true) (oneEach u v) o) := by
  let x := oneEach u v
  let N := n+m
  let z := zeros N
  have hx : x.length = N := oneEach_len u v
  have hz : z.length = N := by simp [z, zeros]
  have hpv := hp.neg rb hx
  have hqv := hq.neg rb hx
  let f := val C x (N+h)
  let g := val C x (N+h')
  have eqV : val (cut C p q (!f) (!g)) x o = val C x o :=
    cut_val_source rb hx hpv.symm hqv.symm o
  have ex (hf : f = true) : g = false := by
    cases hg : g with
    | false => rfl
    | true => exact False.elim <| cones_exclusive rb ro hp.edge hq.edge hne ip iq
                 (hp.lit rb u v hf).1 (hq.lit rb u v hg).1
  have E1 (hf : f = true) (a b : Bool) :
      val (cut C p q a b) x o = val (cut C p q a b) z o := by
    obtain ⟨hu,hv⟩ := hp.lit rb u v hf
    exact cut_zero_of_active rb ro (Or.inl rfl) ho1 (hu.tail hp.edge) (hv.tail hp.edge)
  have E2 (hg : g = true) (a b : Bool) :
      val (cut C p q a b) x o = val (cut C p q a b) z o := by
    obtain ⟨hu,hv⟩ := hq.lit rb u v hg
    exact cut_zero_of_active rb ro (Or.inr rfl) ho2 (hu.tail hq.edge) (hv.tail hq.edge)
  apply scalar_collapse f g _ _ _ _ _ ex
  · intro hf hg
    simpa only [hf,hg,Bool.not_false] using eqV.symm
  · intro hf
    have hg := ex hf
    rw [hf,hg] at eqV
    exact ⟨eqV.symm.trans (E1 hf false true), E1 hf true true⟩
  · intro hg
    have hf : f = false := by cases he : f <;> simp_all
    rw [hf,hg] at eqV
    exact ⟨eqV.symm.trans (E2 hg true false), E2 hg true true⟩
  · apply cut_val_mono rb mono hz hx (by simp) (by simp) _ o
    intro w hw
    simp [z, zeros, List.getD_eq_getElem?_getD, hw]
  · exact cut_val_mono rb mono hz hz (by simp) (by simp) (fun _ _ e => e) o
  · exact cut_val_mono rb mono hz hz (by simp) (by simp) (fun _ _ e => e) o

theorem all_idx (C : Circuit) : (List.range C.gates.length).map (gateAt C) = C.gates := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simpa using gateAt_eq (C := C) h₂

def operands (C : Circuit) (ks : List ℕ) := ks.flatMap (fun j => (gateAt C j).inputs)

theorem ro_iff (C : Circuit) : RO C ↔ (C.gates.flatMap Gate.inputs).Nodup := by
  rw [List.nodup_iff_count_le_one]
  change (∀ w, _ ≤ 1) ↔ ∀ w, _ ≤ 1
  conv_rhs => rw [← all_idx C]
  simp only [List.flatMap_map, List.count_flatMap, List.map_map, Function.comp_def]

theorem ops_ro {C : Circuit} (ro : RO C) :
    (operands C (List.range C.gates.length)).Nodup := by
  have H := (ro_iff C).1 ro
  conv at H => rw [← all_idx C]
  simpa [operands, List.flatMap_map, Function.comp_def] using H

abbrev Closed (N : ℕ) (C : Circuit) (K : Finset ℕ) :=
  ∀ j ∈ K, ∀ w ∈ (gateAt C j).inputs, w < N ∨ w-N ∈ K

def omitted (C : Circuit) (K : Finset ℕ) := Finset.range C.gates.length \ K

theorem keep_mem {C : Circuit} {K : Finset ℕ} {j} :
    j ∈ keepL (omitted C K) C.gates.length ↔ j < C.gates.length ∧ j ∈ K := by
  simp [keepL, omitted]
  omega

theorem closed_conv {N C K} (cl : Closed N C K) :
    ∀ k < C.gates.length, k ∉ omitted C K →
      ∀ i ∈ (gateAt C k).inputs, i < N ∨ i-N ∉ omitted C K := by
  intro k hk hnk i hi
  have hkK : k ∈ K := by simpa [omitted, hk] using hnk
  rcases cl k hkK i hi with h|h
  · exact Or.inl h
  · exact Or.inr (by simp [omitted,h])

theorem rn_inj_kept {N : ℕ} {S : Finset ℕ} {a b} (ha : a < N ∨ a-N ∉ S)
    (hb : b < N ∨ b-N ∉ S) (heq : rn N S a = rn N S b) : a = b := by
  unfold rn at heq
  split_ifs at heq with h h' h' <;> try omega
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt|hlt
  · have hh := rk_lt S (a-N) (b-N) (by omega) (ha.resolve_left h)
    omega
  · have hh := rk_lt S (b-N) (a-N) (by omega) (hb.resolve_left h')
    omega

def pack (N : ℕ) (C : Circuit) (K : Finset ℕ) :=
  Dg N C (omitted C K) C.gates.length

def name (N : ℕ) (C : Circuit) (K : Finset ℕ) (w : ℕ) := rn N (omitted C K) w

theorem pack_inputs (N C K) :
    (pack N C K).flatMap Gate.inputs =
      (operands C (keepL (omitted C K) C.gates.length)).map (name N C K) := by
  simp [pack, Dg, mkG, operands, List.flatMap_map, List.map_flatMap] <;> rfl

theorem kept_valid {N C K w} (cl : Closed N C K)
    (hw : w ∈ operands C (keepL (omitted C K) C.gates.length)) :
    w < N ∨ w-N ∉ omitted C K := by
  obtain ⟨j,hj,hin⟩ := List.mem_flatMap.mp hw
  obtain ⟨hj1,hj2⟩ := keep_mem.mp hj
  exact closed_conv cl j hj1 (by simp [omitted,hj2]) w hin

theorem pack_ro {N C K} (ro : RO C) (cl : Closed N C K) :
    ((pack N C K).flatMap Gate.inputs).Nodup := by
  rw [pack_inputs]
  apply List.Nodup.map_on
  · intro a ha b hb eq
    exact rn_inj_kept (kept_valid cl ha) (kept_valid cl hb) eq
  · exact (ops_ro ro).sublist ((List.filter_sublist).flatMap _)

theorem pack_unused {N C K w} (cl : Closed N C K) (v : w < N ∨ w-N ∈ K)
    (free : ∀ j ∈ K, w ∉ (gateAt C j).inputs) :
    name N C K w ∉ (pack N C K).flatMap Gate.inputs := by
  rw [pack_inputs]
  intro H
  obtain ⟨i,hi,he⟩ := List.mem_map.mp H
  have vw : w < N ∨ w-N ∉ omitted C K := by
    rcases v with h|h
    · exact Or.inl h
    · exact Or.inr (by simp [omitted,h])
  have he' := rn_inj_kept (kept_valid cl hi) vw he
  subst i
  obtain ⟨j,hj,hin⟩ := List.mem_flatMap.mp hi
  exact free j (keep_mem.mp hj).2 hin

theorem pack_rb {N C K} (rb : ReadsBack N C) (cl : Closed N C K) :
    RBo N (pack N C K) := restrict_rb N C _ rb (closed_conv cl) _ le_rfl

theorem pack_size (N C K) :
    (pack N C K).length + (omitted C K).card ≤ C.gates.length := by
  apply restrict_size
  intro j hj
  exact Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1

theorem pack_fan {N C K} (fan : FanInTwo C) (o : ℕ) : FanInTwo ⟨pack N C K,o⟩ := by
  intro g hg
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
  have he := fan _ (keep_gate C _ j hj)
  exact ⟨he.1, by simpa [mkG] using he.2⟩

theorem pack_val {N C K w} (rb : ReadsBack N C) (cl : Closed N C K)
    (hlt : w < N+C.gates.length) (hkeep : w < N ∨ w-N ∈ K)
    {x : List Bool} (hx : x.length = N) :
    (W (pack N C K) x).getD (name N C K w) false = val C x w := by
  apply (restrict_val N C _ rb (closed_conv cl) x hx _ le_rfl).2 w hlt
  rcases hkeep with h|h
  · exact Or.inl h
  · exact Or.inr (by simp [omitted,h])

theorem name_lt {N C K w} (hlt : w < N+C.gates.length) (hkeep : w < N ∨ w-N ∈ K) :
    name N C K w < N+(pack N C K).length := by
  rw [pack,Dg_len]
  apply rn_lt _ _ _ _ hlt
  rcases hkeep with h|h
  · exact Or.inl h
  · exact Or.inr (by simp [omitted,h])

theorem cone_closed {N C h} (rb : ReadsBack N C) (hh : h < C.gates.length) :
    Closed N C (PEqualNP.Core.coneSet N C h) := by
  intro j hj w hw
  obtain ⟨hj',path⟩ := (coneSet_iff_rtg rb hh j).mp hj
  by_cases h0 : w < N
  · exact Or.inl h0
  right
  rw [coneSet_iff_rtg rb hh]
  have hw' := rb j hj' w hw
  refine ⟨by omega, ?_⟩
  rw [show N+(w-N)=w by omega]
  exact path.head (coneRd_of_input hj' hw)

theorem closed_union {N C K L} (a : Closed N C K) (b : Closed N C L) :
    Closed N C (K ∪ L) := by
  intro j hj w hw
  rcases Finset.mem_union.mp hj with hj|hj
  · exact (a j hj w hw).imp_right (Finset.mem_union_left _)
  · exact (b j hj w hw).imp_right (Finset.mem_union_right _)

abbrev OneNot (D : Circuit) :=
  ∀ j < D.gates.length, ∀ j' < D.gates.length,
    (gateAt D j).op = .not → (gateAt D j').op = .not → j = j'

abbrev Answer {n m : ℕ} (A : Fin n → Fin m → Bool) (s : ℕ) :=
  ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ s ∧ Represents A D ∧ ReadsBack (n+m) D ∧ RO D ∧ OneNot D

structure Positive (N : ℕ) (gs : List Gate) : Prop where
  fan : FanInTwo ⟨gs,0⟩
  rb : RBo N gs
  ro : (gs.flatMap Gate.inputs).Nodup
  pos : ∀ g ∈ gs, g.op ≠ .not

theorem pack_positive {N C K} (fan : FanInTwo C) (rb : ReadsBack N C) (ro : RO C)
    (cl : Closed N C K) (pos : ∀ j ∈ K, (gateAt C j).op ≠ .not) :
    Positive N (pack N C K) := by
  refine ⟨pack_fan fan 0,pack_rb rb cl,pack_ro ro cl,?_⟩
  intro g hg
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
  exact pos j (keep_mem.mp hj).2

theorem Positive.emit {n m gs A s o} (H : Positive (n+m) gs) (sz : gs.length+1 ≤ s)
    (ev : ∀ (u : Fin n) (v : Fin m), (W gs (oneEach u v)).getD o false = A u v) :
    Answer A s := by
  let D : Circuit := ⟨gs,o⟩
  refine ⟨D,H.fan,sz,ev,H.rb,(ro_iff D).2 H.ro,?_⟩
  intro j hj j' hj' hn _
  exact (H.pos _ (gateAt_mem hj) hn).elim

theorem Positive.negate {n m gs A s w} (H : Positive (n+m) gs) (sz : gs.length+2 ≤ s)
    (hw : w < n+m+gs.length) (unused : w ∉ gs.flatMap Gate.inputs)
    (ev : ∀ (u : Fin n) (v : Fin m), Bool.not ((W gs (oneEach u v)).getD w false) = A u v) :
    Answer A s := by
  let last : Gate := ⟨.not,[w]⟩
  let D : Circuit := ⟨gs++[last],n+m+gs.length⟩
  have hlen : D.gates.length = gs.length+1 := by simp [D]
  refine ⟨D,?_,by change D.gates.length+1 ≤ s; omega,?_,?_,?_,?_⟩
  · intro g hg
    change g ∈ gs++[last] at hg
    rcases List.mem_append.mp hg with hg|hg
    · exact H.fan g hg
    · obtain rfl := List.mem_singleton.mp hg
      simp [last]
  · intro u v
    rw [eval_W]
    change (W (gs++[last]) (oneEach u v)).getD (n+m+gs.length) false = _
    rw [W_snoc, step_last _ _ _ (by rw [W_length,oneEach_len])]
    exact ev u v
  · exact RBo_append _ _ _ H.rb (RBo_cons _ _ _ (by simpa [last] using hw) (RBo_nil _))
  · apply (ro_iff D).2
    change ((gs++[last]).flatMap Gate.inputs).Nodup
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    change (gs.flatMap Gate.inputs ++ [w]).Nodup
    exact List.nodup_append.mpr ⟨H.ro,by simp,by intro a ha b hb he; obtain rfl := List.mem_singleton.mp hb; exact unused (he ▸ ha)⟩
  · have hnidx (j : ℕ) (hj : j < D.gates.length) (he : (gateAt D j).op = .not) :
        j = gs.length := by
      by_contra hne
      have hl : j < gs.length := by omega
      have eq : gateAt D j = gs[j] := by
        rw [gateAt_eq hj]; exact List.getElem_append_left hl
      exact H.pos _ (List.getElem_mem hl) (eq ▸ he)
    intro j hj k hk a b
    exact (hnidx j hj a).trans (hnidx k hk b).symm

theorem Positive.orGate {N gs} (H : Positive N gs) (ws : List ℕ) (len : ws.length ≤ 2)
    (hw : ∀ w ∈ ws, w < N+gs.length) (nd : ws.Nodup)
    (free : ∀ w ∈ ws, w ∉ gs.flatMap Gate.inputs) :
    Positive N (gs++[⟨.or,ws⟩]) := by
  refine ⟨?_,RBo_append _ _ _ H.rb (RBo_cons _ _ _ hw (RBo_nil _)),?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg|hg
    · exact H.fan g hg
    · obtain rfl := List.mem_singleton.mp hg
      exact ⟨by simp,len⟩
  · simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [List.nodup_append]
    exact ⟨H.ro,nd,fun _ ha _ hb he => free _ hb (he ▸ ha)⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg|hg
    · exact H.pos g hg
    · obtain rfl := List.mem_singleton.mp hg
      change GateOp.or ≠ GateOp.not
      intro e; cases e

theorem Positive.fresh {N gs} (H : Positive N gs) :
    N+gs.length ∉ gs.flatMap Gate.inputs := by
  rintro h
  obtain ⟨g,hg,hin⟩ := List.mem_flatMap.mp h
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hg
  have eq : gs.getD i ⟨.or,[]⟩ = g := (List.getD_eq_getElem _ _ hi).trans he
  have hb := H.rb i hi _ (eq.symm ▸ hin)
  omega

def prefixC (C : Circuit) (k : ℕ) : Circuit := ⟨C.gates.take k,C.output⟩

theorem prefix_length {C k} (hk : k ≤ C.gates.length) : (prefixC C k).gates.length = k := by
  simp [prefixC, hk]

theorem prefix_at {C k j} (hj : j < k) (hk : k ≤ C.gates.length) :
    gateAt (prefixC C k) j = gateAt C j := by
  have h1 : j < (prefixC C k).gates.length := by rw [prefix_length hk]; exact hj
  rw [gateAt_eq h1,gateAt_eq (lt_of_lt_of_le hj hk)]
  exact List.getElem_take

theorem early {n m : ℕ} {A : Fin n → Fin m → Bool} {C s p q} (fan : FanInTwo C) (sz : C.size ≤ s)
    (ev : Represents A C) (rb : ReadsBack (n+m) C) (ro : RO C)
    (hp : p < C.gates.length) (hq : q < C.gates.length)
    (hn : ∀ j < C.gates.length, (gateAt C j).op = .not → j = p ∨ j = q)
    (ho : C.output < n+m+max p q) : Answer A s := by
  let k := max p q
  let D := prefixC C k
  have hlt : k < C.gates.length := max_lt hp hq
  have hlen : D.gates.length = k := prefix_length hlt.le
  have hat (j) (hj : j < D.gates.length) : gateAt D j = gateAt C j :=
    prefix_at (by omega) hlt.le
  refine ⟨D,fun g hg => fan _ (List.mem_of_mem_take hg),?_,?_,?_,?_,?_⟩
  · change D.gates.length+1 ≤ s
    change C.gates.length ≤ s at sz; omega
  · intro u v
    rw [← ev u v, eval_W, eval_W]
    change (W (C.gates.take k) (oneEach u v)).getD C.output false = _
    conv_rhs => rw [← List.take_append_drop k C.gates, W_append]
    symm
    apply W_prefix
    rw [W_length,oneEach_len,List.length_take,Nat.min_eq_left hlt.le]
    exact ho
  · intro j hj i hi
    rw [hat j hj] at hi
    exact rb j (by omega) i hi
  · apply (ro_iff D).2
    exact ((ro_iff C).1 ro).sublist ((List.take_sublist k C.gates).flatMap _)
  · intro j hj j' hj' a b
    rw [hat j hj] at a
    rw [hat j' hj'] at b
    have h1 := hn j (by omega) a
    have h2 := hn j' (by omega) b
    dsimp [k] at hlen
    omega

def treePair (N : ℕ) (C : Circuit) (h k : ℕ) :=
  PEqualNP.Core.coneSet N C h ∪ PEqualNP.Core.coneSet N C k

theorem pair_has_left (N C h k) : h ∈ treePair N C h k := Finset.mem_union_left _ (self_mem_coneSet ..)
theorem pair_has_right (N C h k) : k ∈ treePair N C h k := Finset.mem_union_right _ (self_mem_coneSet ..)

theorem card_two {S : Finset ℕ} {a b} (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) : 2 ≤ S.card := by
  have sub : ({a,b} : Finset ℕ) ⊆ S := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
  have e := Finset.card_le_card sub
  rwa [Finset.card_pair hne] at e

theorem card_three {S : Finset ℕ} {a b c} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ S.card := by
  have sub : ({a,b,c} : Finset ℕ) ⊆ S := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl <;> assumption
  have e := Finset.card_le_card sub
  rwa [Finset.card_triple_eq_three_iff.mpr ⟨hab,hac,hbc⟩] at e

abbrev ClassNot (C : Circuit) (p q : ℕ) :=
  ∀ j < C.gates.length, (gateAt C j).op = .not → j = p ∨ j = q

theorem rest_mono {C p q} (fan : FanInTwo C) (cl : ClassNot C p q) : MonoRest C p q := by
  intro j hj hp hq
  have H := (fan _ (gateAt_mem hj)).1
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at H
  rcases H with e|e|e
  · exact Or.inl e
  · exact Or.inr e
  · exact (cl j hj e).elim (fun he => (hp he).elim) (fun he => (hq he).elim)

theorem edited_fan {C p q a b} (fan : FanInTwo C) : FanInTwo (cut C p q a b) := by
  intro g hg
  obtain ⟨j,hj,he⟩ := List.getElem_of_mem hg
  have H := (gateAt_eq hj).trans he
  have hj2 : j < C.gates.length := by simpa only [cut_len] using hj
  rw [cut_at _ _ _ _ _ hj2] at H
  rw [← H]
  by_cases h : j = p
  · simp only [cutG,if_pos h]; cases a <;> simp [constG]
  by_cases h' : j = q
  · simp only [cutG,if_neg h,if_pos h']; cases b <;> simp [constG]
  simpa only [cutG, if_neg h, if_neg h'] using fan _ (gateAt_mem hj2)

theorem edited_ro {C p q a b} (ro : RO C) : RO (cut C p q a b) := by
  intro w
  rw [cut_len, sum_range_list]
  have htot := ro w
  rw [sum_range_list] at htot
  refine le_trans (Finset.sum_le_sum ?_) htot
  intro j hj
  rw [cut_at _ _ _ _ _ (Finset.mem_range.mp hj)]
  by_cases h : j = p
  · simp only [cutG,if_pos h,constG_inputs,List.count_nil,Nat.zero_le]
  by_cases h' : j = q
  · simp only [cutG,if_neg h,if_pos h',constG_inputs,List.count_nil,Nat.zero_le]
  · simp only [cutG,if_neg h,if_neg h',le_refl]

theorem edited_pos {C p q a b} (cl : ClassNot C p q) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt (cut C p q a b) j).op ≠ .not := by
  rw [cut_at _ _ _ _ _ hj]
  by_cases h : j = p
  · simp only [cutG,if_pos h]; cases a <;> simp [constG]
  by_cases h' : j = q
  · simp only [cutG,if_neg h,if_pos h']; cases b <;> simp [constG]
  simp only [cutG,if_neg h,if_neg h']
  exact fun H => (cl j hj H).elim h h'

theorem Body.unused_else {n m C p h} (B : Body n m C p h) (ro : RO C)
    {j : ℕ} (hj : j < C.gates.length) (hne : j ≠ p) : n+m+h ∉ (gateAt C j).inputs := by
  intro H
  have := edge_unique ro (coneRd_of_input (n := n+m) hj H) B.edge
  omega

theorem cut_const_branch {n m : ℕ} {A : Fin n → Fin m → Bool} {C s p q h o} (B : Body n m C p h)
    (fan : FanInTwo C) (rb : ReadsBack (n+m) C) (ro : RO C) (cl : ClassNot C p q)
    (sz : C.size ≤ s) (ho : o < C.gates.length) (hneq : o ≠ h)
    (ev : ∀ u v, val (cut C p q true true) (oneEach u v) (n+m+o) = A u v) : Answer A s := by
  let N := n+m
  let E := cut C p q true true
  let K := (Finset.range C.gates.length).erase h
  have hl : E.gates.length = C.gates.length := cut_len ..
  have eRB : ReadsBack N E := cut_rb rb
  have hh : h < C.gates.length := lt_trans B.lt B.idx
  have hfree {j} (hj : j < C.gates.length) : N+h ∉ (gateAt E j).inputs := by
    intro hi
    obtain ⟨hjp,_,hin⟩ := cut_inputs hj hi
    exact B.unused_else ro hj hjp hin
  have closedK : Closed N E K := by
    intro j hj w hw
    have hj' := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
    have hlt := eRB j (by rw [hl]; exact hj') w hw
    by_cases h0 : w < N
    · exact Or.inl h0
    · right
      apply Finset.mem_erase.mpr
      refine ⟨?_,Finset.mem_range.mpr (by omega)⟩
      intro he
      have he' : w = N+h := by omega
      exact hfree hj' (he' ▸ hw)
  have HP : Positive N (pack N E K) := pack_positive (edited_fan fan) eRB
    (edited_ro ro) closedK (fun j hj => edited_pos cl (Finset.mem_range.mp (Finset.mem_erase.mp hj).2))
  have hS : h ∈ omitted E K := by simp [omitted,K,hl,hh]
  have hcard : 0 < (omitted E K).card := Finset.card_pos.mpr ⟨h,hS⟩
  have hsz := pack_size N E K
  have hKo : o ∈ K := by simp [K,hneq,ho]
  apply HP.emit (n := n) (m := m) (s := s) (A := A) (o := name N E K (N+o))
  · change C.gates.length ≤ s at sz
    omega
  · intro u v
    exact (pack_val eRB closedK (by omega : N+o < N+E.gates.length)
      (Or.inr (by simpa using hKo)) (oneEach_len u v)).trans (ev u v)

def pick (i : ℕ) (keep : Bool) : List ℕ := if keep then [i] else []

theorem pick_or (i j : ℕ) (a b : Bool) (x : ℕ → Bool) :
    GateOp.or.eval (((pick i a)++(pick j b)).map x) =
      ((x i && a) || (x j && b)) := by
  cases a <;> cases b <;> simp [pick,GateOp.eval]

theorem forest_answer {n m : ℕ} {A : Fin n → Fin m → Bool} {C p q h h' s o} (P : Body n m C p h) (Q : Body n m C q h')
    (rb : ReadsBack (n+m) C) (ro : RO C) (fan : FanInTwo C) (cl : ClassNot C p q)
    (sz : C.size ≤ s) (pq : p ≠ q) (ip : ¬(p=h' ∨ InCone (n+m) C p h'))
    (iq : ¬(q=h ∨ InCone (n+m) C q h)) (ho : o < C.gates.length)
    (caseD :
      (∀ u v, Bool.not (val C (oneEach u v) (n+m+h)) = A u v) ∨
      (∀ u v, Bool.not (val C (oneEach u v) (n+m+h')) = A u v) ∨
      (p < o ∧ q < o ∧ ∃ a b : Bool, ∀ u v,
        Bool.not ((val C (oneEach u v) (n+m+h) && a) || (val C (oneEach u v) (n+m+h') && b)) = A u v)) :
    Answer A s := by
  let N := n+m
  let K := treePair N C h h'
  have hh := lt_trans P.lt P.idx
  have hh' := lt_trans Q.lt Q.idx
  have bounded {j} (hj : j ∈ K) : j < C.gates.length := by
    rcases Finset.mem_union.mp hj with hj|hj
    · exact Finset.mem_range.mp (coneSet_sub_range N C h hh hj)
    · exact Finset.mem_range.mp (coneSet_sub_range N C h' hh' hj)
  have nol : p ∉ K := by
    intro hj
    rcases Finset.mem_union.mp hj with hj|hj
    · have := coneSet_le N C p h hj
      have := P.lt; omega
    · exact ip ((mem_coneSet N C p h').mp hj)
  have nor : q ∉ K := by
    intro hj
    rcases Finset.mem_union.mp hj with hj|hj
    · exact iq ((mem_coneSet N C q h).mp hj)
    · have := coneSet_le N C q h' hj
      have := Q.lt; omega
  have clK : Closed N C K := closed_union (cone_closed rb hh) (cone_closed rb hh')
  have H : Positive N (pack N C K) := pack_positive (N := N) fan rb ro clK (fun j hj e =>
    (cl j (bounded hj) e).elim (fun he => nol (he ▸ hj)) (fun he => nor (he ▸ hj)))
  let gs := pack N C K
  let l := name N C K (N+h)
  let r := name N C K (N+h')
  have KL : h ∈ K := pair_has_left ..
  have KR : h' ∈ K := pair_has_right ..
  have vl : N+h < N+C.gates.length := by omega
  have vr : N+h' < N+C.gates.length := by omega
  have lK : N+h<N ∨ (N+h)-N ∈ K := Or.inr (by simpa using KL)
  have rK : N+h'<N ∨ (N+h')-N ∈ K := Or.inr (by simpa using KR)
  have hl : l < N+gs.length := name_lt vl lK
  have hr : r < N+gs.length := name_lt vr rK
  have fl : l ∉ gs.flatMap Gate.inputs := pack_unused clK lK (fun j hj =>
    P.unused_else ro (bounded hj) (fun he => nol (he ▸ hj)))
  have fr : r ∉ gs.flatMap Gate.inputs := pack_unused clK rK (fun j hj =>
    Q.unused_else ro (bounded hj) (fun he => nor (he ▸ hj)))
  have L (u : Fin n) (v : Fin m) : (W gs (oneEach u v)).getD l false = val C (oneEach u v) (N+h) :=
    pack_val rb clK vl lK (oneEach_len u v)
  have R (u : Fin n) (v : Fin m) : (W gs (oneEach u v)).getD r false = val C (oneEach u v) (N+h') :=
    pack_val rb clK vr rK (oneEach_len u v)
  have dropL : p ∈ omitted C K := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr P.idx,nol⟩
  have dropR : q ∈ omitted C K := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr Q.idx,nor⟩
  have size := pack_size N C K
  change gs.length + (omitted C K).card ≤ C.gates.length at size
  change C.gates.length ≤ s at sz
  have two := card_two dropL dropR pq
  rcases caseD with ev|ev|⟨po,qo,a,b,ev⟩
  · apply H.negate (n := n) (m := m) (s := s) (A := A) (w := l) (by change gs.length+2 ≤ s; omega) hl fl
    intro u v
    exact (congrArg Bool.not (L u v)).trans (ev u v)
  · apply H.negate (n := n) (m := m) (s := s) (A := A) (w := r) (by change gs.length+2 ≤ s; omega) hr fr
    intro u v
    exact (congrArg Bool.not (R u v)).trans (ev u v)
  · have dro : o ∈ omitted C K := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_range.mpr ho,?_⟩
      intro mem
      rcases Finset.mem_union.mp mem with mem|mem
      · have := coneSet_le N C o h mem; have := P.lt; omega
      · have := coneSet_le N C o h' mem; have := Q.lt; omega
    have three := card_three dropL dropR dro pq (by omega) (by omega)
    have lr : l ≠ r := by
      intro he
      have ha : N+h<N ∨ (N+h)-N ∉ omitted C K := Or.inr (by simp [omitted,KL])
      have hb : N+h'<N ∨ (N+h')-N ∉ omitted C K := Or.inr (by simp [omitted,KR])
      have he2 := rn_inj_kept ha hb he
      have e : h=h' := by omega
      have e' := P.edge
      rw [e] at e'
      have := edge_unique ro e' Q.edge
      omega
    let ws := pick l a ++ pick r b
    have Hws : ws.length ≤ 2 ∧ ws.Nodup ∧ (∀ i ∈ ws, i=l ∨ i=r) := by
      cases a <;> cases b <;> simp [ws,pick,lr] <;> grind
    have H' := H.orGate ws Hws.1 (fun i hi => (Hws.2.2 i hi).elim
        (fun he => he.symm ▸ hl) (fun he => he.symm ▸ hr)) Hws.2.1
        (fun i hi => (Hws.2.2 i hi).elim (fun he => he.symm ▸ fl) (fun he => he.symm ▸ fr))
    let mid := N+gs.length
    have readFree : mid ∉ (gs++[(⟨GateOp.or,ws⟩ : Gate)]).flatMap Gate.inputs := by
      simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_append,not_or]
      refine ⟨H.fresh,?_⟩
      intro hmem
      have := Hws.2.2 mid hmem
      change N+gs.length = l ∨ N+gs.length = r at this
      omega
    apply H'.negate (n := n) (m := m) (A := A) (s := s) (w := mid)
      (by change (gs++[(⟨GateOp.or, ws⟩ : Gate)]).length+2 ≤ s; simp only [List.length_append,List.length_singleton]; omega)
      (by change N+gs.length < N+(gs++[(⟨GateOp.or, ws⟩ : Gate)]).length; simp only [List.length_append,List.length_singleton]; omega) readFree
    intro u v
    change Bool.not ((W (gs++[⟨.or,ws⟩]) (oneEach u v)).getD mid false) = _
    rw [W_snoc,step_last _ _ _ (by simp [mid,W_length,oneEach_len,N])]
    change Bool.not (GateOp.or.eval ((pick l a ++ pick r b).map _)) = _
    rw [pick_or,L,R]
    exact ev u v

theorem empty_pos (N : ℕ) : Positive N [] := by
  refine ⟨?_,RBo_nil _,by simp,?_⟩
  · intro g hg; exact (List.not_mem_nil hg).elim
  · intro g hg; exact (List.not_mem_nil hg).elim

theorem deletion {n m s : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {p q h h' : ℕ}
    (fan : FanInTwo C) (sz : C.size ≤ s) (ev : Represents A C) (rb : ReadsBack (n+m) C)
    (ro : RO C) (P : Body n m C p h) (Q : Body n m C q h') (pq : p ≠ q)
    (cl : ClassNot C p q) (ip : ¬(p=h' ∨ InCone (n+m) C p h'))
    (iq : ¬(q=h ∨ InCone (n+m) C q h)) : Answer A s := by
  let N := n+m
  have hsz : C.gates.length ≤ s := sz
  by_cases hbad : N+C.gates.length ≤ C.output
  · apply (empty_pos N).emit (n := n) (m := m) (A := A) (s := s) (o := N) (by change 0+1 ≤ s; have := P.idx; omega)
    intro u v
    rw [← ev u v, eval_eq_val, val_ge (oneEach_len u v) hbad,W_nil]
    exact List.getD_eq_default _ _ (by rw [oneEach_len])
  by_cases hEarly : C.output < N+max p q
  · exact early fan sz ev rb ro P.idx Q.idx cl hEarly
  obtain ⟨o,ho⟩ : ∃ o, C.output = N+o := ⟨C.output-N,by omega⟩
  have ho' : o < C.gates.length := by omega
  have po : p ≤ o := by omega
  have qo : q ≤ o := by omega
  have out (u : Fin n) (v : Fin m) : val C (oneEach u v) (N+o) = A u v := by
    rw [← ho]; exact ev u v
  have finish := forest_answer (A := A) P Q rb ro fan cl sz pq ip iq ho'
  by_cases ep : o = p
  · apply finish
    left; intro u v
    have he := P.neg rb (oneEach_len u v)
    exact he.symm.trans (by simpa only [ep] using out u v)
  by_cases eq : o = q
  · apply finish
    right; left; intro u v
    have he := Q.neg rb (oneEach_len u v)
    exact he.symm.trans (by simpa only [eq] using out u v)
  let sem := fun (u : Fin n) (v : Fin m) => cofactor (o := N+o) P Q rb ro (rest_mono fan cl) pq ip iq
      (by change N+p ≤ N+o; omega) (by change N+q ≤ N+o; omega) u v
  cases ec : zeroCof N C p q (N+o) true true with
  | false =>
    apply cut_const_branch P fan rb ro cl sz ho' (by have := P.lt; omega)
    intro u v
    have he := sem u v
    rw [show zeroCof (n+m) C p q (N+o) true true = false from ec] at he
    exact he.symm.trans (out u v)
  | true =>
    apply finish
    right; right
    refine ⟨by omega,by omega,!(zeroCof N C p q (N+o) false true),
      !(zeroCof N C p q (N+o) true false),?_⟩
    intro u v
    have he := sem u v
    rw [show zeroCof (n+m) C p q (N+o) true true = true from ec] at he
    exact he.symm.trans (out u v)

end PEqualNP.Outside.L_meta_25465.Chriesistei

open PEqualNP.Outside.L_meta_25465.Chriesistei in

theorem PEqualNP.Outside.L_meta_25465 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (p q h h' : ℕ), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → (∀ w : ℕ, ((List.range C.gates.length).map (fun r => (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs.count w)).sum ≤ 1) → p < C.gates.length → q < C.gates.length → p ≠ q → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt C q).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).inputs.head? = some (n + m + h) → (PEqualNP.MetaComplexity.NestedCover.gateAt C q).inputs.head? = some (n + m + h') → h < p → h' < q → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.not → j = p ∨ j = q) → ¬ (p = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C p h') → ¬ (q = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C q h) → (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + h) false = true → (∃ i : ℕ, (i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∧ u.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs) ∧ (∃ i : ℕ, (i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∧ (n + v.val) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs)) → (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + h') false = true → (∃ i : ℕ, (i = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h') ∧ u.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs) ∧ (∃ i : ℕ, (i = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h') ∧ (n + v.val) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + 1 ≤ s ∧ PEqualNP.Represents.Represents A D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) D ∧ (∀ w : ℕ, ((List.range D.gates.length).map (fun r => (PEqualNP.MetaComplexity.NestedCover.gateAt D r).inputs.count w)).sum ≤ 1) ∧ (∀ j < D.gates.length, ∀ j' < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt D j').op = PEqualNP.CircuitLowerBounds.GateOp.not → j = j') := by
  intro n m s A C p q h h' fan sz ev rb ro hp hq pq pn qn ph qh pl ql cl ip iq crp crq
  exact deletion fan sz ev rb ro ⟨hp,pn,ph,pl,crp⟩ ⟨hq,qn,qh,ql,crq⟩ pq cl ip iq
