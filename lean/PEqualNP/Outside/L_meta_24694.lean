import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24694

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def IsGoodGate (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1)

def FanInTwoNot1Gate (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length ≤ 1)

def FanInTwoNot1 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, FanInTwoNot1Gate g

def Reduced (N : ℕ) (C : Circuit) : Prop :=
  ((∀ g ∈ C.gates, IsGoodGate g) ∧
    ReadsBack N C ∧
    0 < C.size ∧
    C.output + 1 = N + C.size ∧
    (∀ j < C.size, readsIn C (Finset.range C.size) (N + j) = 0 ↔ j + 1 = C.size)) ∨
  (C.size = 0 ∧ C.output < N)

def Listed (C : Circuit) (w : ℕ) : Prop :=
  (∃ g ∈ C.gates, w ∈ g.inputs) ∨ C.output = w

def NonConst {n m : ℕ} (A : Fin n → Fin m → Bool) : Prop :=
  ∃ (u u2 : Fin n) (v v2 : Fin m), A u v ≠ A u2 v2

theorem fanInTwo_of_not1 {C : Circuit} (h : FanInTwoNot1 C) : FanInTwo C := by
  intro g hg
  rcases h g hg with ⟨h1 | h1, hlen⟩ | ⟨h1, hlen⟩
  · exact ⟨by simp [h1], hlen⟩
  · exact ⟨by simp [h1], hlen⟩
  · exact ⟨by simp [h1], by omega⟩

theorem fanInTwoNot1_of_reduced {N : ℕ} {C : Circuit} (h : Reduced N C) : FanInTwoNot1 C := by
  rcases h with ⟨hGood, _, _, _, _⟩ | ⟨h0, _⟩
  · intro g hg
    rcases hGood g hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr ⟨h1, by omega⟩
  · intro g hg
    have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero h0
    rw [hnil] at hg
    cases hg

theorem fanInTwo_of_reduced {N : ℕ} {C : Circuit} (h : Reduced N C) : FanInTwo C :=
  fanInTwo_of_not1 (fanInTwoNot1_of_reduced h)

theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_oob (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem getD_append_left (w1 w2 : List Bool) (i : ℕ) (hi : i < w1.length) :
    (w1 ++ w2).getD i false = w1.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_singleton_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem foldl_step_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (step w g).length := by simp [step]; omega
    rw [ih (step w g) hi', step, getD_append_left w _ i hi]

theorem gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq_getElem C j hj]
  exact List.getElem_mem hj

theorem mem_gates_iff_gateAt (C : Circuit) (g : Gate) :
    g ∈ C.gates ↔ ∃ j < C.size, gateAt C j = g := by
  constructor
  · intro hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact ⟨j, hj, gateAt_eq_getElem C j hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact gateAt_mem C j hj

theorem foldl_split (gs : List Gate) (j : ℕ) (hj : j < gs.length) (w0 : List Bool) :
    gs.foldl step w0 = (gs.drop (j + 1)).foldl step (step ((gs.take j).foldl step w0) gs[j]) := by
  conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
  rw [List.foldl_append, List.foldl_cons]

theorem take_fold_length (gs : List Gate) (j : ℕ) (hj : j < gs.length) (w0 : List Bool) :
    ((gs.take j).foldl step w0).length = w0.length + j := by
  rw [foldl_step_length, List.length_take]
  omega

theorem wires_gate_val (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (x : List Bool) :
    (C.wires x).getD (x.length + j) false =
      let Wp := (C.gates.take j).foldl step x
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => Wp.getD i false) := by
  rw [wires_eq_foldl, foldl_split C.gates j hj x]
  have hlen := take_fold_length C.gates j hj x
  set Wp := (C.gates.take j).foldl step x
  have hlt : x.length + j < (step Wp C.gates[j]).length := by simp [step, hlen]
  rw [foldl_step_getD _ _ _ hlt]
  unfold step
  rw [← hlen, getD_append_singleton_last, gateAt_eq_getElem C j hj]

theorem wires_gate_lt (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (x : List Bool)
    (i : ℕ) (hi : i < x.length + j) :
    (C.wires x).getD i false = ((C.gates.take j).foldl step x).getD i false := by
  rw [wires_eq_foldl, foldl_split C.gates j hj x]
  have hlen := take_fold_length C.gates j hj x
  set Wp := (C.gates.take j).foldl step x
  have hlt : i < (step Wp C.gates[j]).length := by simp [step, hlen]; omega
  rw [foldl_step_getD _ _ _ hlt, step, getD_append_left Wp _ i (by omega)]

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [getD_append_left _ _ i (by simp [hi])]
  simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff]

theorem oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (h1 : n ≤ i) (h2 : i < n + m) :
    (oneEach u v).getD i false = decide (i - n = v.val) := by
  unfold oneEach
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_ofFn]
  have hlt : i - n < m := by omega
  simp [hlt, Fin.ext_iff]

theorem not_const_eval {n m : ℕ} {A : Fin n → Fin m → Bool} (hNC : NonConst A)
    {C : Circuit} (hRep : Represents A C) (b : Bool)
    (hAll : ∀ u : Fin n, ∀ v : Fin m, C.eval (oneEach u v) = b) : False := by
  obtain ⟨u, u2, v, v2, hne⟩ := hNC
  have h1 := hRep u v
  have h2 := hRep u2 v2
  rw [hAll u v] at h1
  rw [hAll u2 v2] at h2
  exact hne (h1.symm.trans h2)

theorem readsIn_range_eq_zero_iff (C : Circuit) (w : ℕ) :
    readsIn C (Finset.range C.size) w = 0 ↔ ∀ j < C.size, w ∉ (gateAt C j).inputs := by
  unfold readsIn
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h j hj
    exact List.count_eq_zero.mp (h j (Finset.mem_range.mpr hj))
  · intro h j hj
    exact List.count_eq_zero.mpr (h j (Finset.mem_range.mp hj))

theorem readsBack_last_unread (N : ℕ) (C : Circuit) (hRB : ReadsBack N C) (j : ℕ)
    (hj : j + 1 = C.size) : readsIn C (Finset.range C.size) (N + j) = 0 := by
  rw [readsIn_range_eq_zero_iff]
  intro k hk hmem
  have hlt := hRB k hk (N + j) hmem
  simp only [Circuit.size] at hk hj
  omega

def shiftDown (m i : ℕ) : ℕ :=
  if i < m then i else i - 1

def sig (m u i : ℕ) : ℕ :=
  if i < m then i else if i = m then u else i - 1

def rd (m u : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (sig m u)⟩

def shiftGate (m : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftDown m)⟩

def substTrueGate (m : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => ⟨GateOp.and, (g.inputs.filter (fun i => decide (i ≠ m))).map (shiftDown m)⟩
  | GateOp.or =>
      if m ∈ g.inputs then ⟨GateOp.and, []⟩
      else ⟨GateOp.or, g.inputs.map (shiftDown m)⟩
  | GateOp.not =>
      match g.inputs with
      | [] => ⟨GateOp.not, []⟩
      | a :: _ => if a = m then ⟨GateOp.or, []⟩ else ⟨GateOp.not, [shiftDown m a]⟩
  | _ => g

def substFalseGate (m : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.or => ⟨GateOp.or, (g.inputs.filter (fun i => decide (i ≠ m))).map (shiftDown m)⟩
  | GateOp.and =>
      if m ∈ g.inputs then ⟨GateOp.or, []⟩
      else ⟨GateOp.and, g.inputs.map (shiftDown m)⟩
  | GateOp.not =>
      match g.inputs with
      | [] => ⟨GateOp.not, []⟩
      | a :: _ => if a = m then ⟨GateOp.and, []⟩ else ⟨GateOp.not, [shiftDown m a]⟩
  | _ => g

theorem length_filter_ne_lt {l : List ℕ} {m : ℕ} (hm : m ∈ l) :
    (l.filter (fun i => decide (i ≠ m))).length < l.length := by
  induction l with
  | nil => cases hm
  | cons a t ih =>
    simp only [List.mem_cons] at hm
    rw [List.filter_cons]
    by_cases ha : a = m
    · subst ha
      have hd : decide (a ≠ a) = false := decide_eq_false (not_not.mpr rfl)
      rw [hd]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have := List.length_filter_le (fun i => decide (i ≠ a)) t
      omega
    · have hd : decide (a ≠ m) = true := decide_eq_true ha
      rw [hd]
      simp only [↓reduceIte, List.length_cons]
      rcases hm with rfl | ht
      · exact absurd rfl ha
      · have := ih ht
        omega

theorem fanInTwoNot1_substTrueGate (m : ℕ) (g : Gate) (hg : FanInTwoNot1Gate g) :
    FanInTwoNot1Gate (substTrueGate m g) := by
  rcases hg with ⟨h1 | h1, hlen⟩ | ⟨h1, hlen⟩
  · simp only [substTrueGate, h1]
    left
    refine ⟨Or.inl rfl, ?_⟩
    simp only [List.length_map]
    have := List.length_filter_le (fun i => decide (i ≠ m)) g.inputs
    omega
  · simp only [substTrueGate, h1]
    split_ifs
    · exact Or.inl ⟨Or.inl rfl, by simp⟩
    · exact Or.inl ⟨Or.inr rfl, by simp [hlen]⟩
  · simp only [substTrueGate, h1]
    cases hins : g.inputs with
    | nil => exact Or.inr ⟨rfl, by simp⟩
    | cons a t =>
      dsimp only
      split_ifs
      · exact Or.inl ⟨Or.inr rfl, by simp⟩
      · exact Or.inr ⟨rfl, by simp⟩

theorem fanInTwoNot1_substFalseGate (m : ℕ) (g : Gate) (hg : FanInTwoNot1Gate g) :
    FanInTwoNot1Gate (substFalseGate m g) := by
  rcases hg with ⟨h1 | h1, hlen⟩ | ⟨h1, hlen⟩
  · simp only [substFalseGate, h1]
    split_ifs
    · exact Or.inl ⟨Or.inr rfl, by simp⟩
    · exact Or.inl ⟨Or.inl rfl, by simp [hlen]⟩
  · simp only [substFalseGate, h1]
    left
    refine ⟨Or.inr rfl, ?_⟩
    simp only [List.length_map]
    have := List.length_filter_le (fun i => decide (i ≠ m)) g.inputs
    omega
  · simp only [substFalseGate, h1]
    cases hins : g.inputs with
    | nil => exact Or.inr ⟨rfl, by simp⟩
    | cons a t =>
      dsimp only
      split_ifs
      · exact Or.inl ⟨Or.inl rfl, by simp⟩
      · exact Or.inr ⟨rfl, by simp⟩

theorem substTrueGate_mem (m : ℕ) (g : Gate) (hg : FanInTwoNot1Gate g) {w : ℕ}
    (hw : w ∈ (substTrueGate m g).inputs) :
    ∃ i ∈ g.inputs, i ≠ m ∧ w = shiftDown m i := by
  rcases hg with ⟨h1 | h1, _⟩ | ⟨h1, _⟩
  · simp only [substTrueGate, h1, List.mem_map, List.mem_filter, decide_eq_true_eq] at hw
    obtain ⟨i, ⟨hi, hne⟩, rfl⟩ := hw
    exact ⟨i, hi, hne, rfl⟩
  · simp only [substTrueGate, h1] at hw
    split_ifs at hw with hm
    · simp at hw
    · simp only [List.mem_map] at hw
      obtain ⟨i, hi, rfl⟩ := hw
      exact ⟨i, hi, fun heq => hm (heq ▸ hi), rfl⟩
  · simp only [substTrueGate, h1] at hw
    cases hins : g.inputs with
    | nil => rw [hins] at hw; simp at hw
    | cons a t =>
      rw [hins] at hw
      dsimp only at hw
      split_ifs at hw with ha
      · simp at hw
      · simp only [List.mem_singleton] at hw
        exact ⟨a, by simp, ha, hw⟩

theorem substFalseGate_mem (m : ℕ) (g : Gate) (hg : FanInTwoNot1Gate g) {w : ℕ}
    (hw : w ∈ (substFalseGate m g).inputs) :
    ∃ i ∈ g.inputs, i ≠ m ∧ w = shiftDown m i := by
  rcases hg with ⟨h1 | h1, _⟩ | ⟨h1, _⟩
  · simp only [substFalseGate, h1] at hw
    split_ifs at hw with hm
    · simp at hw
    · simp only [List.mem_map] at hw
      obtain ⟨i, hi, rfl⟩ := hw
      exact ⟨i, hi, fun heq => hm (heq ▸ hi), rfl⟩
  · simp only [substFalseGate, h1, List.mem_map, List.mem_filter, decide_eq_true_eq] at hw
    obtain ⟨i, ⟨hi, hne⟩, rfl⟩ := hw
    exact ⟨i, hi, hne, rfl⟩
  · simp only [substFalseGate, h1] at hw
    cases hins : g.inputs with
    | nil => rw [hins] at hw; simp at hw
    | cons a t =>
      rw [hins] at hw
      dsimp only at hw
      split_ifs at hw with ha
      · simp at hw
      · simp only [List.mem_singleton] at hw
        exact ⟨a, by simp, ha, hw⟩

theorem substFalseGate_mem_of_not_mem (m : ℕ) (g : Gate) (hg : FanInTwoNot1Gate g)
    (hm : m ∉ g.inputs) {i : ℕ} (hi : i ∈ g.inputs) :
    shiftDown m i ∈ (substFalseGate m g).inputs := by
  have hne : i ≠ m := fun heq => hm (heq ▸ hi)
  rcases hg with ⟨h1 | h1, _⟩ | ⟨h1, hlen⟩
  · simp only [substFalseGate, h1, hm, ↓reduceIte, List.mem_map]
    exact ⟨i, hi, rfl⟩
  · simp only [substFalseGate, h1, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨i, ⟨hi, hne⟩, rfl⟩
  · simp only [substFalseGate, h1]
    cases hins : g.inputs with
    | nil => rw [hins] at hi; cases hi
    | cons a t =>
      cases t with
      | nil =>
        rw [hins, List.mem_singleton] at hi
        subst hi
        simp [hne]
      | cons _ _ =>
        rw [hins] at hlen; simp at hlen

theorem not_isGoodGate_substTrueGate_of_mem (m : ℕ) (g : Gate) (hg : FanInTwoNot1Gate g)
    (hm : m ∈ g.inputs) : ¬ IsGoodGate (substTrueGate m g) := by
  rcases hg with ⟨h1 | h1, hlen⟩ | ⟨h1, hlen⟩
  · simp only [substTrueGate, h1, IsGoodGate]
    have hlt := length_filter_ne_lt hm
    simp only [List.length_map]
    rintro (⟨_, h2⟩ | ⟨h2, _⟩)
    · omega
    · cases h2
  · simp only [substTrueGate, h1, hm, ↓reduceIte, IsGoodGate]
    simp
  · simp only [substTrueGate, h1]
    cases hins : g.inputs with
    | nil => rw [hins] at hm; cases hm
    | cons a t =>
      cases t with
      | nil =>
        rw [hins, List.mem_singleton] at hm
        subst hm
        simp [IsGoodGate]
      | cons _ _ =>
        rw [hins] at hlen; simp at hlen

theorem not_isGoodGate_substFalseGate_of_mem (m : ℕ) (g : Gate) (hg : FanInTwoNot1Gate g)
    (hm : m ∈ g.inputs) : ¬ IsGoodGate (substFalseGate m g) := by
  rcases hg with ⟨h1 | h1, hlen⟩ | ⟨h1, hlen⟩
  · simp only [substFalseGate, h1, hm, ↓reduceIte, IsGoodGate]
    simp
  · simp only [substFalseGate, h1, IsGoodGate]
    have hlt := length_filter_ne_lt hm
    simp only [List.length_map]
    rintro (⟨_, h2⟩ | ⟨h2, _⟩)
    · omega
    · cases h2
  · simp only [substFalseGate, h1]
    cases hins : g.inputs with
    | nil => rw [hins] at hm; cases hm
    | cons a t =>
      cases t with
      | nil =>
        rw [hins, List.mem_singleton] at hm
        subst hm
        simp [IsGoodGate]
      | cons _ _ =>
        rw [hins] at hlen; simp at hlen

theorem not_isGoodGate_substTrueGate_of_not_good (m : ℕ) (g : Gate) (hg : FanInTwoNot1Gate g)
    (hng : ¬ IsGoodGate g) : ¬ IsGoodGate (substTrueGate m g) := by
  rcases hg with ⟨h1 | h1, hlen⟩ | ⟨h1, hlen⟩
  · have hlt : g.inputs.length < 2 := by
      by_contra hge
      exact hng (Or.inl ⟨Or.inl h1, by omega⟩)
    simp only [substTrueGate, h1, IsGoodGate, List.length_map]
    have hfl := List.length_filter_le (fun i => decide (i ≠ m)) g.inputs
    rintro (⟨_, h2⟩ | ⟨h2, _⟩)
    · omega
    · cases h2
  · have hlt : g.inputs.length < 2 := by
      by_contra hge
      exact hng (Or.inl ⟨Or.inr h1, by omega⟩)
    simp only [substTrueGate, h1]
    split_ifs
    · simp [IsGoodGate]
    · simp only [IsGoodGate, List.length_map]
      rintro (⟨_, h2⟩ | ⟨h2, _⟩)
      · omega
      · cases h2
  · have h0 : g.inputs.length = 0 := by
      by_contra hne
      exact hng (Or.inr ⟨h1, by omega⟩)
    have hnil : g.inputs = [] := List.eq_nil_of_length_eq_zero h0
    simp [substTrueGate, h1, hnil, IsGoodGate]

theorem not_isGoodGate_substFalseGate_of_not_good (m : ℕ) (g : Gate) (hg : FanInTwoNot1Gate g)
    (hng : ¬ IsGoodGate g) : ¬ IsGoodGate (substFalseGate m g) := by
  rcases hg with ⟨h1 | h1, hlen⟩ | ⟨h1, hlen⟩
  · have hlt : g.inputs.length < 2 := by
      by_contra hge
      exact hng (Or.inl ⟨Or.inl h1, by omega⟩)
    simp only [substFalseGate, h1]
    split_ifs
    · simp [IsGoodGate]
    · simp only [IsGoodGate, List.length_map]
      rintro (⟨_, h2⟩ | ⟨h2, _⟩)
      · omega
      · cases h2
  · have hlt : g.inputs.length < 2 := by
      by_contra hge
      exact hng (Or.inl ⟨Or.inr h1, by omega⟩)
    simp only [substFalseGate, h1, IsGoodGate, List.length_map]
    have hfl := List.length_filter_le (fun i => decide (i ≠ m)) g.inputs
    rintro (⟨_, h2⟩ | ⟨h2, _⟩)
    · omega
    · cases h2
  · have h0 : g.inputs.length = 0 := by
      by_contra hne
      exact hng (Or.inr ⟨h1, by omega⟩)
    have hnil : g.inputs = [] := List.eq_nil_of_length_eq_zero h0
    simp [substFalseGate, h1, hnil, IsGoodGate]

def RelCopy (m u : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length + 1 ∧ m < a.length ∧ ∀ i, b.getD (sig m u i) false = a.getD i false

theorem relCopy_step (m u : ℕ) (hu : u < m) (a b : List Bool) (g : Gate) (h : RelCopy m u a b) :
    RelCopy m u (step a g) (step b (rd m u g)) := by
  obtain ⟨hl, hm, hv⟩ := h
  have hev : (rd m u g).op.eval ((rd m u g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    simp only [rd, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hv i
  unfold step
  rw [hev]
  refine ⟨by simp [hl], by simp; omega, ?_⟩
  intro i
  rcases Nat.lt_trichotomy i a.length with h1 | h1 | h1
  · have hs : sig m u i < b.length := by unfold sig; split_ifs <;> omega
    rw [getD_append_left _ _ _ hs, getD_append_left _ _ _ h1, hv]
  · have hs : sig m u i = b.length := by unfold sig; split_ifs <;> omega
    rw [hs, getD_append_singleton_last, h1, getD_append_singleton_last]
  · have hs : sig m u i > b.length := by unfold sig; split_ifs <;> omega
    rw [getD_oob _ _ (by simp; omega), getD_oob _ _ (by simp; omega)]

theorem relCopy_fold (m u : ℕ) (hu : u < m) (gs : List Gate) :
    ∀ a b : List Bool, RelCopy m u a b →
      RelCopy m u (gs.foldl step a) ((gs.map (rd m u)).foldl step b) := by
  induction gs with
  | nil => intro a b h; exact h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons, List.map_cons]
    exact ih _ _ (relCopy_step m u hu a b g h)

def delCopy (N j y : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (rd (N + j) y), sig (N + j) y C.output⟩

theorem delCopy_size (N j y : ℕ) (C : Circuit) (hj : j < C.size) :
    (delCopy N j y C).size + 1 = C.size := by
  simp only [Circuit.size] at hj ⊢
  simp only [delCopy, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem delCopy_fanInTwoNot1 (N j y : ℕ) (C : Circuit) (hF : FanInTwoNot1 C) :
    FanInTwoNot1 (delCopy N j y C) := by
  intro g hg
  simp only [delCopy, List.mem_append, List.mem_map] at hg
  rcases hg with h1 | ⟨g0, h2, rfl⟩
  · exact hF g (List.mem_of_mem_take h1)
  · have := hF g0 (List.mem_of_mem_drop h2)
    simpa [FanInTwoNot1Gate, rd] using this

theorem delCopy_eval (N j y : ℕ) (C : Circuit) (hj : j < C.size) (hy : y < N + j)
    (x : List Bool) (hx : x.length = N)
    (hcopy : (C.wires x).getD (N + j) false = (C.wires x).getD y false) :
    (delCopy N j y C).eval x = C.eval x := by
  unfold Circuit.eval
  have hlen := take_fold_length C.gates j hj x
  rw [hx] at hlen
  set Wp := (C.gates.take j).foldl step x with hWp
  have hW : C.wires x = (C.gates.drop (j + 1)).foldl step (step Wp C.gates[j]) := by
    rw [wires_eq_foldl, foldl_split C.gates j hj x]
  have hD : (delCopy N j y C).wires x =
      ((C.gates.drop (j + 1)).map (rd (N + j) y)).foldl step Wp := by
    rw [wires_eq_foldl]
    simp only [delCopy, List.foldl_append, hWp]
  have hvk : (step Wp C.gates[j]).getD (N + j) false = Wp.getD y false := by
    rw [hW, foldl_step_getD _ _ _ (by simp [step, hlen]),
      foldl_step_getD _ _ _ (by simp [step, hlen]; omega)] at hcopy
    rw [hcopy, step, getD_append_left Wp _ y (by omega)]
  have hrel0 : RelCopy (N + j) y (step Wp C.gates[j]) Wp := by
    refine ⟨by simp [step], by simp [step, hlen], ?_⟩
    intro i
    rcases Nat.lt_trichotomy i (N + j) with h1 | h1 | h1
    · have hs : sig (N + j) y i = i := by simp [sig, h1]
      rw [hs, step, getD_append_left Wp _ i (by omega)]
    · have hs : sig (N + j) y i = y := by simp [sig, h1]
      rw [hs, h1, hvk]
    · have hs : sig (N + j) y i = i - 1 := by unfold sig; split_ifs <;> omega
      rw [hs, getD_oob Wp _ (by omega), getD_oob _ _ (by simp [step, hlen]; omega)]
  have hrel := relCopy_fold (N + j) y hy (C.gates.drop (j + 1)) _ _ hrel0
  rw [hD, hW]
  exact hrel.2.2 C.output

theorem delCopy_listed (N j y : ℕ) (C : Circuit) (hj : j < C.size)
    (hy : y ∈ (gateAt C j).inputs) (w : ℕ) (hw : w < N)
    (hL : Listed (delCopy N j y C) w) : Listed C w := by
  have hmemj : gateAt C j ∈ C.gates := gateAt_mem C j hj
  rcases hL with ⟨g, hg, hwg⟩ | hout
  · simp only [delCopy, List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, h2, rfl⟩
    · exact Or.inl ⟨g, List.mem_of_mem_take h1, hwg⟩
    · simp only [rd, List.mem_map] at hwg
      obtain ⟨i, hi, hsig⟩ := hwg
      unfold sig at hsig
      split_ifs at hsig with hlt heq
      · subst hsig
        exact Or.inl ⟨g0, List.mem_of_mem_drop h2, hi⟩
      · subst hsig
        exact Or.inl ⟨gateAt C j, hmemj, hy⟩
      · omega
  · simp only [delCopy] at hout
    unfold sig at hout
    split_ifs at hout with hlt heq
    · exact Or.inr hout
    · subst hout
      exact Or.inl ⟨gateAt C j, hmemj, hy⟩
    · omega

def RelConst (m : ℕ) (bval : Bool) (a b : List Bool) : Prop :=
  a.length = b.length + 1 ∧ m < a.length ∧ a.getD m false = bval ∧
    ∀ i, i ≠ m → b.getD (shiftDown m i) false = a.getD i false

theorem relConst_append (m : ℕ) (bval : Bool) (a b : List Bool) (v : Bool)
    (h : RelConst m bval a b) : RelConst m bval (a ++ [v]) (b ++ [v]) := by
  obtain ⟨hl, hm, hbm, hv⟩ := h
  refine ⟨by simp [hl], by simp; omega, ?_, ?_⟩
  · rw [getD_append_left a [v] m hm, hbm]
  · intro i hne
    rcases Nat.lt_trichotomy i a.length with h1 | h1 | h1
    · have hs : shiftDown m i < b.length := by unfold shiftDown; split_ifs <;> omega
      rw [getD_append_left _ _ _ hs, getD_append_left _ _ _ h1, hv i hne]
    · have hs : shiftDown m i = b.length := by unfold shiftDown; split_ifs <;> omega
      rw [hs, getD_append_singleton_last, h1, getD_append_singleton_last]
    · have hs : shiftDown m i > b.length := by unfold shiftDown; split_ifs <;> omega
      rw [getD_oob _ _ (by simp; omega), getD_oob _ _ (by simp; omega)]

theorem relTrue_step (m : ℕ) (a b : List Bool) (g : Gate) (hg : FanInTwoNot1Gate g)
    (h : RelConst m true a b) :
    RelConst m true (step a g) (step b (substTrueGate m g)) := by
  obtain ⟨hl, hm, hbm, hv⟩ := h
  have hev : (substTrueGate m g).op.eval ((substTrueGate m g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    rcases hg with ⟨h1 | h1, _⟩ | ⟨h1, _⟩
    · simp only [substTrueGate, h1, GateOp.eval]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id_eq,
        forall_exists_index, and_imp]
      constructor
      · intro hL _ i hi rfl
        by_cases him : i = m
        · subst him; exact hbm
        · rw [← hv i him]
          exact hL _ _ i hi him rfl rfl
      · intro hR _ _ i hi hne rfl rfl
        rw [hv i hne]
        exact hR _ i hi rfl
    · simp only [substTrueGate, h1]
      split_ifs with hmin
      · simp only [GateOp.eval, List.map_nil, List.all_nil]
        symm
        rw [List.any_eq_true]
        exact ⟨true, List.mem_map.mpr ⟨m, hmin, hbm⟩, rfl⟩
      · simp only [GateOp.eval, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hv i (fun heq => hmin (heq ▸ hi))
    · simp only [substTrueGate, h1]
      cases hins : g.inputs with
      | nil => simp [GateOp.eval]
      | cons x t =>
        dsimp only
        split_ifs with hx
        · subst hx
          simp only [GateOp.eval, List.map_nil, List.any_nil, List.map_cons, List.headD_cons, hbm]
          rfl
        · simp only [GateOp.eval, List.map_cons, List.headD_cons, hv x hx]
  unfold step
  rw [hev]
  exact relConst_append m true a b _ ⟨hl, hm, hbm, hv⟩

theorem relFalse_step (m : ℕ) (a b : List Bool) (g : Gate) (hg : FanInTwoNot1Gate g)
    (h : RelConst m false a b) :
    RelConst m false (step a g) (step b (substFalseGate m g)) := by
  obtain ⟨hl, hm, hbm, hv⟩ := h
  have hev : (substFalseGate m g).op.eval ((substFalseGate m g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    rcases hg with ⟨h1 | h1, _⟩ | ⟨h1, _⟩
    · simp only [substFalseGate, h1]
      split_ifs with hmin
      · simp only [GateOp.eval, List.map_nil, List.any_nil]
        symm
        rw [Bool.eq_false_iff]
        intro hall
        rw [List.all_eq_true] at hall
        have := hall false (List.mem_map.mpr ⟨m, hmin, hbm⟩)
        cases this
      · simp only [GateOp.eval, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hv i (fun heq => hmin (heq ▸ hi))
    · simp only [substFalseGate, h1, GateOp.eval]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id_eq]
      constructor
      · rintro ⟨_, ⟨_, ⟨i, ⟨hi, hne⟩, rfl⟩, rfl⟩, htrue⟩
        rw [hv i hne] at htrue
        exact ⟨true, ⟨i, hi, htrue⟩, rfl⟩
      · rintro ⟨_, ⟨i, hi, rfl⟩, htrue⟩
        have hne : i ≠ m := by
          intro heq
          subst heq
          rw [hbm] at htrue
          cases htrue
        refine ⟨true, ⟨shiftDown m i, ⟨i, ⟨hi, hne⟩, rfl⟩, ?_⟩, rfl⟩
        rw [hv i hne]
        exact htrue
    · simp only [substFalseGate, h1]
      cases hins : g.inputs with
      | nil => simp [GateOp.eval]
      | cons x t =>
        dsimp only
        split_ifs with hx
        · subst hx
          simp only [GateOp.eval, List.map_nil, List.all_nil, List.map_cons, List.headD_cons, hbm]
          rfl
        · simp only [GateOp.eval, List.map_cons, List.headD_cons, hv x hx]
  unfold step
  rw [hev]
  exact relConst_append m false a b _ ⟨hl, hm, hbm, hv⟩

theorem relTrue_fold (m : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, FanInTwoNot1Gate g) :
    ∀ a b : List Bool, RelConst m true a b →
      RelConst m true (gs.foldl step a) ((gs.map (substTrueGate m)).foldl step b) := by
  induction gs with
  | nil => intro a b h; exact h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons, List.map_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) _ _
      (relTrue_step m a b g (hgs g (List.mem_cons_self ..)) h)

theorem relFalse_fold (m : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, FanInTwoNot1Gate g) :
    ∀ a b : List Bool, RelConst m false a b →
      RelConst m false (gs.foldl step a) ((gs.map (substFalseGate m)).foldl step b) := by
  induction gs with
  | nil => intro a b h; exact h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons, List.map_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) _ _
      (relFalse_step m a b g (hgs g (List.mem_cons_self ..)) h)

def delConstTrue (N j : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substTrueGate (N + j)),
    shiftDown (N + j) C.output⟩

def delConstFalse (N j : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substFalseGate (N + j)),
    shiftDown (N + j) C.output⟩

theorem delConstTrue_size (N j : ℕ) (C : Circuit) (hj : j < C.size) :
    (delConstTrue N j C).size + 1 = C.size := by
  simp only [Circuit.size] at hj ⊢
  simp only [delConstTrue, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem delConstFalse_size (N j : ℕ) (C : Circuit) (hj : j < C.size) :
    (delConstFalse N j C).size + 1 = C.size := by
  simp only [Circuit.size] at hj ⊢
  simp only [delConstFalse, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem delConstTrue_fanInTwoNot1 (N j : ℕ) (C : Circuit) (hF : FanInTwoNot1 C) :
    FanInTwoNot1 (delConstTrue N j C) := by
  intro g hg
  simp only [delConstTrue, List.mem_append, List.mem_map] at hg
  rcases hg with h1 | ⟨g0, h2, rfl⟩
  · exact hF g (List.mem_of_mem_take h1)
  · exact fanInTwoNot1_substTrueGate (N + j) g0 (hF g0 (List.mem_of_mem_drop h2))

theorem delConstFalse_fanInTwoNot1 (N j : ℕ) (C : Circuit) (hF : FanInTwoNot1 C) :
    FanInTwoNot1 (delConstFalse N j C) := by
  intro g hg
  simp only [delConstFalse, List.mem_append, List.mem_map] at hg
  rcases hg with h1 | ⟨g0, h2, rfl⟩
  · exact hF g (List.mem_of_mem_take h1)
  · exact fanInTwoNot1_substFalseGate (N + j) g0 (hF g0 (List.mem_of_mem_drop h2))

theorem delConstTrue_eval (N j : ℕ) (C : Circuit) (hF : FanInTwoNot1 C) (hj : j < C.size)
    (hout : C.output ≠ N + j) (x : List Bool) (hx : x.length = N)
    (hval : (C.wires x).getD (N + j) false = true) :
    (delConstTrue N j C).eval x = C.eval x := by
  unfold Circuit.eval
  have hlen := take_fold_length C.gates j hj x
  rw [hx] at hlen
  set Wp := (C.gates.take j).foldl step x with hWp
  have hW : C.wires x = (C.gates.drop (j + 1)).foldl step (step Wp C.gates[j]) := by
    rw [wires_eq_foldl, foldl_split C.gates j hj x]
  have hD : (delConstTrue N j C).wires x =
      ((C.gates.drop (j + 1)).map (substTrueGate (N + j))).foldl step Wp := by
    rw [wires_eq_foldl]
    simp only [delConstTrue, List.foldl_append, hWp]
  have hvk : (step Wp C.gates[j]).getD (N + j) false = true := by
    rw [hW, foldl_step_getD _ _ _ (by simp [step, hlen])] at hval
    exact hval
  have hrel0 : RelConst (N + j) true (step Wp C.gates[j]) Wp := by
    refine ⟨by simp [step], by simp [step, hlen], hvk, ?_⟩
    intro i hne
    rcases Nat.lt_trichotomy i (N + j) with h1 | h1 | h1
    · have hs : shiftDown (N + j) i = i := by simp [shiftDown, h1]
      rw [hs, step, getD_append_left Wp _ i (by omega)]
    · exact absurd h1 hne
    · have hs : shiftDown (N + j) i = i - 1 := by unfold shiftDown; split_ifs <;> omega
      rw [hs, getD_oob Wp _ (by omega), getD_oob _ _ (by simp [step, hlen]; omega)]
  have hrel := relTrue_fold (N + j) (C.gates.drop (j + 1))
    (fun g hg => hF g (List.mem_of_mem_drop hg)) _ _ hrel0
  rw [hD, hW]
  exact hrel.2.2.2 C.output hout

theorem delConstFalse_eval (N j : ℕ) (C : Circuit) (hF : FanInTwoNot1 C) (hj : j < C.size)
    (hout : C.output ≠ N + j) (x : List Bool) (hx : x.length = N)
    (hval : (C.wires x).getD (N + j) false = false) :
    (delConstFalse N j C).eval x = C.eval x := by
  unfold Circuit.eval
  have hlen := take_fold_length C.gates j hj x
  rw [hx] at hlen
  set Wp := (C.gates.take j).foldl step x with hWp
  have hW : C.wires x = (C.gates.drop (j + 1)).foldl step (step Wp C.gates[j]) := by
    rw [wires_eq_foldl, foldl_split C.gates j hj x]
  have hD : (delConstFalse N j C).wires x =
      ((C.gates.drop (j + 1)).map (substFalseGate (N + j))).foldl step Wp := by
    rw [wires_eq_foldl]
    simp only [delConstFalse, List.foldl_append, hWp]
  have hvk : (step Wp C.gates[j]).getD (N + j) false = false := by
    rw [hW, foldl_step_getD _ _ _ (by simp [step, hlen])] at hval
    exact hval
  have hrel0 : RelConst (N + j) false (step Wp C.gates[j]) Wp := by
    refine ⟨by simp [step], by simp [step, hlen], hvk, ?_⟩
    intro i hne
    rcases Nat.lt_trichotomy i (N + j) with h1 | h1 | h1
    · have hs : shiftDown (N + j) i = i := by simp [shiftDown, h1]
      rw [hs, step, getD_append_left Wp _ i (by omega)]
    · exact absurd h1 hne
    · have hs : shiftDown (N + j) i = i - 1 := by unfold shiftDown; split_ifs <;> omega
      rw [hs, getD_oob Wp _ (by omega), getD_oob _ _ (by simp [step, hlen]; omega)]
  have hrel := relFalse_fold (N + j) (C.gates.drop (j + 1))
    (fun g hg => hF g (List.mem_of_mem_drop hg)) _ _ hrel0
  rw [hD, hW]
  exact hrel.2.2.2 C.output hout

theorem shiftDown_eq_lt {N j i w : ℕ} (hw : w < N) (hne : i ≠ N + j)
    (heq : shiftDown (N + j) i = w) : i = w := by
  unfold shiftDown at heq
  split_ifs at heq <;> omega

theorem delConstTrue_listed (N j : ℕ) (C : Circuit) (hF : FanInTwoNot1 C)
    (hout : C.output ≠ N + j) (w : ℕ) (hw : w < N)
    (hL : Listed (delConstTrue N j C) w) : Listed C w := by
  rcases hL with ⟨g, hg, hwg⟩ | ho
  · simp only [delConstTrue, List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, h2, rfl⟩
    · exact Or.inl ⟨g, List.mem_of_mem_take h1, hwg⟩
    · obtain ⟨i, hi, hne, hsh⟩ := substTrueGate_mem (N + j) g0 (hF g0 (List.mem_of_mem_drop h2)) hwg
      have hiw := shiftDown_eq_lt hw hne hsh.symm
      subst hiw
      exact Or.inl ⟨g0, List.mem_of_mem_drop h2, hi⟩
  · simp only [delConstTrue] at ho
    exact Or.inr (shiftDown_eq_lt hw hout ho)

theorem delConstFalse_listed (N j : ℕ) (C : Circuit) (hF : FanInTwoNot1 C)
    (hout : C.output ≠ N + j) (w : ℕ) (hw : w < N)
    (hL : Listed (delConstFalse N j C) w) : Listed C w := by
  rcases hL with ⟨g, hg, hwg⟩ | ho
  · simp only [delConstFalse, List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, h2, rfl⟩
    · exact Or.inl ⟨g, List.mem_of_mem_take h1, hwg⟩
    · obtain ⟨i, hi, hne, hsh⟩ := substFalseGate_mem (N + j) g0 (hF g0 (List.mem_of_mem_drop h2)) hwg
      have hiw := shiftDown_eq_lt hw hne hsh.symm
      subst hiw
      exact Or.inl ⟨g0, List.mem_of_mem_drop h2, hi⟩
  · simp only [delConstFalse] at ho
    exact Or.inr (shiftDown_eq_lt hw hout ho)

def RelSkip (m : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length + 1 ∧ m < a.length ∧
    ∀ i, i ≠ m → b.getD (shiftDown m i) false = a.getD i false

theorem relSkip_step (m : ℕ) (a b : List Bool) (g : Gate) (hnm : m ∉ g.inputs)
    (h : RelSkip m a b) : RelSkip m (step a g) (step b (shiftGate m g)) := by
  obtain ⟨hl, hm, hv⟩ := h
  have hev : (shiftGate m g).op.eval ((shiftGate m g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    simp only [shiftGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hv i (fun heq => hnm (heq ▸ hi))
  unfold step
  rw [hev]
  refine ⟨by simp [hl], by simp; omega, ?_⟩
  intro i hne
  rcases Nat.lt_trichotomy i a.length with h1 | h1 | h1
  · have hs : shiftDown m i < b.length := by unfold shiftDown; split_ifs <;> omega
    rw [getD_append_left _ _ _ hs, getD_append_left _ _ _ h1, hv i hne]
  · have hs : shiftDown m i = b.length := by unfold shiftDown; split_ifs <;> omega
    rw [hs, getD_append_singleton_last, h1, getD_append_singleton_last]
  · have hs : shiftDown m i > b.length := by unfold shiftDown; split_ifs <;> omega
    rw [getD_oob _ _ (by simp; omega), getD_oob _ _ (by simp; omega)]

theorem relSkip_fold (m : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, m ∉ g.inputs) :
    ∀ a b : List Bool, RelSkip m a b →
      RelSkip m (gs.foldl step a) ((gs.map (shiftGate m)).foldl step b) := by
  induction gs with
  | nil => intro a b h; exact h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons, List.map_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) _ _
      (relSkip_step m a b g (hgs g (List.mem_cons_self ..)) h)

def delSkip (N j : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (shiftGate (N + j)),
    shiftDown (N + j) C.output⟩

theorem delSkip_size (N j : ℕ) (C : Circuit) (hj : j < C.size) :
    (delSkip N j C).size + 1 = C.size := by
  simp only [Circuit.size] at hj ⊢
  simp only [delSkip, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem delSkip_fanInTwoNot1 (N j : ℕ) (C : Circuit) (hF : FanInTwoNot1 C) :
    FanInTwoNot1 (delSkip N j C) := by
  intro g hg
  simp only [delSkip, List.mem_append, List.mem_map] at hg
  rcases hg with h1 | ⟨g0, h2, rfl⟩
  · exact hF g (List.mem_of_mem_take h1)
  · have := hF g0 (List.mem_of_mem_drop h2)
    simpa [FanInTwoNot1Gate, shiftGate] using this

theorem delSkip_eval (N j : ℕ) (C : Circuit) (hj : j < C.size)
    (hun : ∀ k < C.size, N + j ∉ (gateAt C k).inputs)
    (hout : C.output ≠ N + j) (x : List Bool) (hx : x.length = N) :
    (delSkip N j C).eval x = C.eval x := by
  unfold Circuit.eval
  have hlen := take_fold_length C.gates j hj x
  rw [hx] at hlen
  set Wp := (C.gates.take j).foldl step x with hWp
  have hW : C.wires x = (C.gates.drop (j + 1)).foldl step (step Wp C.gates[j]) := by
    rw [wires_eq_foldl, foldl_split C.gates j hj x]
  have hD : (delSkip N j C).wires x =
      ((C.gates.drop (j + 1)).map (shiftGate (N + j))).foldl step Wp := by
    rw [wires_eq_foldl]
    simp only [delSkip, List.foldl_append, hWp]
  have hrel0 : RelSkip (N + j) (step Wp C.gates[j]) Wp := by
    refine ⟨by simp [step], by simp [step, hlen], ?_⟩
    intro i hne
    rcases Nat.lt_trichotomy i (N + j) with h1 | h1 | h1
    · have hs : shiftDown (N + j) i = i := by simp [shiftDown, h1]
      rw [hs, step, getD_append_left Wp _ i (by omega)]
    · exact absurd h1 hne
    · have hs : shiftDown (N + j) i = i - 1 := by unfold shiftDown; split_ifs <;> omega
      rw [hs, getD_oob Wp _ (by omega), getD_oob _ _ (by simp [step, hlen]; omega)]
  have hdrop : ∀ g ∈ C.gates.drop (j + 1), N + j ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := (mem_gates_iff_gateAt C g).mp (List.mem_of_mem_drop hg)
    exact hun k hk
  have hrel := relSkip_fold (N + j) (C.gates.drop (j + 1)) hdrop _ _ hrel0
  rw [hD, hW]
  exact hrel.2.2 C.output hout

theorem delSkip_listed (N j : ℕ) (C : Circuit)
    (hun : ∀ k < C.size, N + j ∉ (gateAt C k).inputs)
    (hout : C.output ≠ N + j) (w : ℕ) (hw : w < N)
    (hL : Listed (delSkip N j C) w) : Listed C w := by
  rcases hL with ⟨g, hg, hwg⟩ | ho
  · simp only [delSkip, List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, h2, rfl⟩
    · exact Or.inl ⟨g, List.mem_of_mem_take h1, hwg⟩
    · simp only [shiftGate, List.mem_map] at hwg
      obtain ⟨i, hi, hsh⟩ := hwg
      obtain ⟨k, hk, hgk⟩ := (mem_gates_iff_gateAt C g0).mp (List.mem_of_mem_drop h2)
      have hne : i ≠ N + j := fun heq => hun k hk (hgk.symm ▸ heq ▸ hi)
      have hiw := shiftDown_eq_lt hw hne hsh
      subst hiw
      exact Or.inl ⟨g0, List.mem_of_mem_drop h2, hi⟩
  · simp only [delSkip] at ho
    exact Or.inr (shiftDown_eq_lt hw hout ho)

theorem output_ne_of_const_gate {n m : ℕ} {A : Fin n → Fin m → Bool} (hNC : NonConst A)
    {C : Circuit} (hRep : Represents A C) (j : ℕ) (b : Bool)
    (hval : ∀ x : List Bool, x.length = n + m → (C.wires x).getD (n + m + j) false = b) :
    C.output ≠ n + m + j := by
  intro ho
  apply not_const_eval hNC hRep b
  intro u v
  unfold Circuit.eval
  rw [ho]
  exact hval (oneEach u v) (oneEach_length u v)

theorem reduce_step {n m : ℕ} {A : Fin n → Fin m → Bool} (hNC : NonConst A)
    (C : Circuit) (hF : FanInTwoNot1 C) (hRep : Represents A C)
    (hPos : 0 < C.size) (hNotRed : ¬ Reduced (n + m) C) :
    ∃ C' : Circuit,
      FanInTwoNot1 C' ∧
      Represents A C' ∧
      C'.size + 1 = C.size ∧
      (∀ w < n + m, Listed C' w → Listed C w) := by
  set N := n + m with hNdef
  by_cases hRB : ReadsBack N C
  · by_cases hGood : ∀ g ∈ C.gates, IsGoodGate g
    · by_cases hOut : C.output + 1 = N + C.size
      · have hNotReads : ¬ ∀ j < C.size,
            readsIn C (Finset.range C.size) (N + j) = 0 ↔ j + 1 = C.size := by
          intro hr
          exact hNotRed (Or.inl ⟨hGood, hRB, hPos, hOut, hr⟩)
        push Not at hNotReads
        obtain ⟨j, hj, hbad⟩ := hNotReads
        rcases hbad with ⟨hz, hjl⟩ | ⟨hnz, heq⟩
        · have hun : ∀ k < C.size, N + j ∉ (gateAt C k).inputs :=
            (readsIn_range_eq_zero_iff C (N + j)).mp hz
          have hout : C.output ≠ N + j := by omega
          refine ⟨delSkip N j C, delSkip_fanInTwoNot1 N j C hF, ?_,
            delSkip_size N j C hj, fun w hw => delSkip_listed N j C hun hout w hw⟩
          intro u v
          rw [delSkip_eval N j C hj hun hout (oneEach u v) (oneEach_length u v)]
          exact hRep u v
        · exact absurd (readsBack_last_unread N C hRB j heq) hnz
      · have hlt : C.output < N + C.size := by
          by_contra hge
          push Not at hge
          apply not_const_eval hNC hRep false
          intro u v
          unfold Circuit.eval
          apply getD_oob
          rw [wires_eq_foldl, foldl_step_length, oneEach_length]
          exact hge
        set j := C.size - 1 with hjdef
        have hj : j < C.size := by omega
        have hun : ∀ k < C.size, N + j ∉ (gateAt C k).inputs := by
          intro k hk hmem
          have := hRB k hk (N + j) hmem
          simp only [Circuit.size] at hk hjdef
          omega
        have hout : C.output ≠ N + j := by omega
        refine ⟨delSkip N j C, delSkip_fanInTwoNot1 N j C hF, ?_,
          delSkip_size N j C hj, fun w hw => delSkip_listed N j C hun hout w hw⟩
        intro u v
        rw [delSkip_eval N j C hj hun hout (oneEach u v) (oneEach_length u v)]
        exact hRep u v
    · push Not at hGood
      obtain ⟨g, hg, hng⟩ := hGood
      obtain ⟨j, hj, hgj⟩ := (mem_gates_iff_gateAt C g).mp hg
      have hFg : FanInTwoNot1Gate (gateAt C j) := hF _ (gateAt_mem C j hj)
      rw [← hgj] at hng
      rcases hFg with ⟨hop | hop, hlen⟩ | ⟨hop, hlen⟩
      · cases hins : (gateAt C j).inputs with
        | nil =>
          have hval : ∀ x : List Bool, x.length = N → (C.wires x).getD (N + j) false = true := by
            intro x hx
            rw [← hx, wires_gate_val C j hj x]
            simp [hop, hins, GateOp.eval]
          have hout := output_ne_of_const_gate hNC hRep j true hval
          refine ⟨delConstTrue N j C, delConstTrue_fanInTwoNot1 N j C hF, ?_,
            delConstTrue_size N j C hj, fun w hw => delConstTrue_listed N j C hF hout w hw⟩
          intro u v
          rw [delConstTrue_eval N j C hF hj hout (oneEach u v) (oneEach_length u v)
            (hval _ (oneEach_length u v))]
          exact hRep u v
        | cons a t =>
          cases t with
          | nil =>
            have ha : a < N + j := hRB j hj a (by simp [hins])
            have hcopy : ∀ x : List Bool, x.length = N →
                (C.wires x).getD (N + j) false = (C.wires x).getD a false := by
              intro x hx
              rw [← hx, wires_gate_val C j hj x, wires_gate_lt C j hj x a (by omega)]
              simp [hop, hins, GateOp.eval]
            refine ⟨delCopy N j a C, delCopy_fanInTwoNot1 N j a C hF, ?_,
              delCopy_size N j a C hj,
              fun w hw => delCopy_listed N j a C hj (by simp [hins]) w hw⟩
            intro u v
            rw [delCopy_eval N j a C hj ha (oneEach u v) (oneEach_length u v)
              (hcopy _ (oneEach_length u v))]
            exact hRep u v
          | cons b t2 =>
            cases t2 with
            | nil =>
              exfalso
              exact hng (Or.inl ⟨Or.inl hop, by simp [hins]⟩)
            | cons _ _ =>
              rw [hins] at hlen; simp at hlen
      · cases hins : (gateAt C j).inputs with
        | nil =>
          have hval : ∀ x : List Bool, x.length = N → (C.wires x).getD (N + j) false = false := by
            intro x hx
            rw [← hx, wires_gate_val C j hj x]
            simp [hop, hins, GateOp.eval]
          have hout := output_ne_of_const_gate hNC hRep j false hval
          refine ⟨delConstFalse N j C, delConstFalse_fanInTwoNot1 N j C hF, ?_,
            delConstFalse_size N j C hj, fun w hw => delConstFalse_listed N j C hF hout w hw⟩
          intro u v
          rw [delConstFalse_eval N j C hF hj hout (oneEach u v) (oneEach_length u v)
            (hval _ (oneEach_length u v))]
          exact hRep u v
        | cons a t =>
          cases t with
          | nil =>
            have ha : a < N + j := hRB j hj a (by simp [hins])
            have hcopy : ∀ x : List Bool, x.length = N →
                (C.wires x).getD (N + j) false = (C.wires x).getD a false := by
              intro x hx
              rw [← hx, wires_gate_val C j hj x, wires_gate_lt C j hj x a (by omega)]
              simp [hop, hins, GateOp.eval]
            refine ⟨delCopy N j a C, delCopy_fanInTwoNot1 N j a C hF, ?_,
              delCopy_size N j a C hj,
              fun w hw => delCopy_listed N j a C hj (by simp [hins]) w hw⟩
            intro u v
            rw [delCopy_eval N j a C hj ha (oneEach u v) (oneEach_length u v)
              (hcopy _ (oneEach_length u v))]
            exact hRep u v
          | cons b t2 =>
            cases t2 with
            | nil =>
              exfalso
              exact hng (Or.inl ⟨Or.inr hop, by simp [hins]⟩)
            | cons _ _ =>
              rw [hins] at hlen; simp at hlen
      · cases hins : (gateAt C j).inputs with
        | nil =>
          have hval : ∀ x : List Bool, x.length = N → (C.wires x).getD (N + j) false = true := by
            intro x hx
            rw [← hx, wires_gate_val C j hj x]
            simp [hop, hins, GateOp.eval]
          have hout := output_ne_of_const_gate hNC hRep j true hval
          refine ⟨delConstTrue N j C, delConstTrue_fanInTwoNot1 N j C hF, ?_,
            delConstTrue_size N j C hj, fun w hw => delConstTrue_listed N j C hF hout w hw⟩
          intro u v
          rw [delConstTrue_eval N j C hF hj hout (oneEach u v) (oneEach_length u v)
            (hval _ (oneEach_length u v))]
          exact hRep u v
        | cons a t =>
          cases t with
          | nil =>
            exfalso
            exact hng (Or.inr ⟨hop, by simp [hins]⟩)
          | cons _ _ =>
            rw [hins] at hlen; simp at hlen
  · unfold ReadsBack at hRB
    push Not at hRB
    obtain ⟨j, hj, i, hi, hge⟩ := hRB
    have hFg : FanInTwoNot1Gate (gateAt C j) := hF _ (gateAt_mem C j hj)
    rcases hFg with ⟨hop | hop, hlen⟩ | ⟨hop, hlen⟩
    · have hval : ∀ x : List Bool, x.length = N → (C.wires x).getD (N + j) false = false := by
        intro x hx
        rw [← hx, wires_gate_val C j hj x]
        simp only [hop, GateOp.eval]
        rw [Bool.eq_false_iff]
        intro hall
        rw [List.all_eq_true] at hall
        have hlenW := take_fold_length C.gates j hj x
        have hoob : ((C.gates.take j).foldl step x).getD i false = false :=
          getD_oob _ i (by omega)
        have := hall false (List.mem_map.mpr ⟨i, hi, hoob⟩)
        cases this
      have hout := output_ne_of_const_gate hNC hRep j false hval
      refine ⟨delConstFalse N j C, delConstFalse_fanInTwoNot1 N j C hF, ?_,
        delConstFalse_size N j C hj, fun w hw => delConstFalse_listed N j C hF hout w hw⟩
      intro u v
      rw [delConstFalse_eval N j C hF hj hout (oneEach u v) (oneEach_length u v)
        (hval _ (oneEach_length u v))]
      exact hRep u v
    · cases hins : (gateAt C j).inputs with
      | nil => rw [hins] at hi; cases hi
      | cons a t =>
        cases t with
        | nil =>
          rw [hins, List.mem_singleton] at hi
          subst hi
          have hval : ∀ x : List Bool, x.length = N → (C.wires x).getD (N + j) false = false := by
            intro x hx
            rw [← hx, wires_gate_val C j hj x]
            have hlenW := take_fold_length C.gates j hj x
            have hoob : ((C.gates.take j).foldl step x).getD i false = false :=
              getD_oob _ i (by omega)
            simp only [hop, hins, GateOp.eval, List.map_cons, List.map_nil, hoob]
            rfl
          have hout := output_ne_of_const_gate hNC hRep j false hval
          refine ⟨delConstFalse N j C, delConstFalse_fanInTwoNot1 N j C hF, ?_,
            delConstFalse_size N j C hj, fun w hw => delConstFalse_listed N j C hF hout w hw⟩
          intro u v
          rw [delConstFalse_eval N j C hF hj hout (oneEach u v) (oneEach_length u v)
            (hval _ (oneEach_length u v))]
          exact hRep u v
        | cons b t2 =>
          cases t2 with
          | nil =>
            by_cases ha : a < N + j
            · have hb : N + j ≤ b := by
                rw [hins] at hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl <;> omega
              have hcopy : ∀ x : List Bool, x.length = N →
                  (C.wires x).getD (N + j) false = (C.wires x).getD a false := by
                intro x hx
                rw [← hx, wires_gate_val C j hj x, wires_gate_lt C j hj x a (by omega)]
                have hlenW := take_fold_length C.gates j hj x
                have hoob : ((C.gates.take j).foldl step x).getD b false = false :=
                  getD_oob _ b (by omega)
                simp only [hop, hins, GateOp.eval, List.map_cons, List.map_nil, hoob]
                simp
              refine ⟨delCopy N j a C, delCopy_fanInTwoNot1 N j a C hF, ?_,
                delCopy_size N j a C hj,
                fun w hw => delCopy_listed N j a C hj (by simp [hins]) w hw⟩
              intro u v
              rw [delCopy_eval N j a C hj ha (oneEach u v) (oneEach_length u v)
                (hcopy _ (oneEach_length u v))]
              exact hRep u v
            · by_cases hb : b < N + j
              · have hcopy : ∀ x : List Bool, x.length = N →
                    (C.wires x).getD (N + j) false = (C.wires x).getD b false := by
                  intro x hx
                  rw [← hx, wires_gate_val C j hj x, wires_gate_lt C j hj x b (by omega)]
                  have hlenW := take_fold_length C.gates j hj x
                  have hoob : ((C.gates.take j).foldl step x).getD a false = false :=
                    getD_oob _ a (by omega)
                  simp only [hop, hins, GateOp.eval, List.map_cons, List.map_nil, hoob]
                  simp
                refine ⟨delCopy N j b C, delCopy_fanInTwoNot1 N j b C hF, ?_,
                  delCopy_size N j b C hj,
                  fun w hw => delCopy_listed N j b C hj (by simp [hins]) w hw⟩
                intro u v
                rw [delCopy_eval N j b C hj hb (oneEach u v) (oneEach_length u v)
                  (hcopy _ (oneEach_length u v))]
                exact hRep u v
              · have hval : ∀ x : List Bool, x.length = N → (C.wires x).getD (N + j) false = false := by
                  intro x hx
                  rw [← hx, wires_gate_val C j hj x]
                  have hlenW := take_fold_length C.gates j hj x
                  have ha0 : ((C.gates.take j).foldl step x).getD a false = false :=
                    getD_oob _ a (by omega)
                  have hb0 : ((C.gates.take j).foldl step x).getD b false = false :=
                    getD_oob _ b (by omega)
                  simp only [hop, hins, GateOp.eval, List.map_cons, List.map_nil, ha0, hb0]
                  rfl
                have hout := output_ne_of_const_gate hNC hRep j false hval
                refine ⟨delConstFalse N j C, delConstFalse_fanInTwoNot1 N j C hF, ?_,
                  delConstFalse_size N j C hj, fun w hw => delConstFalse_listed N j C hF hout w hw⟩
                intro u v
                rw [delConstFalse_eval N j C hF hj hout (oneEach u v) (oneEach_length u v)
                  (hval _ (oneEach_length u v))]
                exact hRep u v
          | cons _ _ =>
            rw [hins] at hlen; simp at hlen
    · cases hins : (gateAt C j).inputs with
      | nil => rw [hins] at hi; cases hi
      | cons a t =>
        cases t with
        | nil =>
          rw [hins, List.mem_singleton] at hi
          subst hi
          have hval : ∀ x : List Bool, x.length = N → (C.wires x).getD (N + j) false = true := by
            intro x hx
            rw [← hx, wires_gate_val C j hj x]
            have hlenW := take_fold_length C.gates j hj x
            have hoob : ((C.gates.take j).foldl step x).getD i false = false :=
              getD_oob _ i (by omega)
            simp only [hop, hins, GateOp.eval, List.map_cons, List.map_nil, hoob]
            rfl
          have hout := output_ne_of_const_gate hNC hRep j true hval
          refine ⟨delConstTrue N j C, delConstTrue_fanInTwoNot1 N j C hF, ?_,
            delConstTrue_size N j C hj, fun w hw => delConstTrue_listed N j C hF hout w hw⟩
          intro u v
          rw [delConstTrue_eval N j C hF hj hout (oneEach u v) (oneEach_length u v)
            (hval _ (oneEach_length u v))]
          exact hRep u v
        | cons _ _ =>
          rw [hins] at hlen; simp at hlen

theorem reduce_circuit {n m : ℕ} {A : Fin n → Fin m → Bool} (hNC : NonConst A) :
    ∀ s (C : Circuit), C.size ≤ s → FanInTwoNot1 C → Represents A C →
      ∃ D : Circuit,
        Reduced (n + m) D ∧
        Represents A D ∧
        D.size ≤ C.size ∧
        (∀ w < n + m, Listed D w → Listed C w) ∧
        (D.size + 1 ≤ C.size ∨ (Reduced (n + m) C ∧ ∀ w < n + m, Listed C w → Listed D w)) := by
  intro s
  induction s with
  | zero =>
    intro C hs hF hRep
    have h0 : C.size = 0 := by omega
    have hout : C.output < n + m := by
      by_contra hge
      push Not at hge
      apply not_const_eval hNC hRep false
      intro u v
      unfold Circuit.eval
      apply getD_oob
      rw [wires_eq_foldl, foldl_step_length, oneEach_length]
      have : C.gates.length = 0 := h0
      omega
    have hRed : Reduced (n + m) C := Or.inr ⟨h0, hout⟩
    exact ⟨C, hRed, hRep, le_rfl, fun _ _ h => h, Or.inr ⟨hRed, fun _ _ h => h⟩⟩
  | succ s ih =>
    intro C hs hF hRep
    by_cases hRed : Reduced (n + m) C
    · exact ⟨C, hRed, hRep, le_rfl, fun _ _ h => h, Or.inr ⟨hRed, fun _ _ h => h⟩⟩
    · have hPos : 0 < C.size := by
        by_contra h0
        have h0' : C.size = 0 := by omega
        have hout : C.output < n + m := by
          by_contra hge
          push Not at hge
          apply not_const_eval hNC hRep false
          intro u v
          unfold Circuit.eval
          apply getD_oob
          rw [wires_eq_foldl, foldl_step_length, oneEach_length]
          have : C.gates.length = 0 := h0'
          omega
        exact hRed (Or.inr ⟨h0', hout⟩)
      obtain ⟨C', hF', hRep', hSz', hL'⟩ := reduce_step hNC C hF hRep hPos hRed
      obtain ⟨D, hRedD, hRepD, hSzD, hLD, _⟩ := ih C' (by omega) hF' hRep'
      exact ⟨D, hRedD, hRepD, by omega, fun w hw h => hL' w hw (hLD w hw h), Or.inl (by omega)⟩

theorem succAbove_val {n : ℕ} (k : Fin (n + 1)) (u : Fin n) :
    (k.succAbove u).val = if u.val < k.val then u.val else u.val + 1 := by
  by_cases h : u.val < k.val
  · have hlt : u.castSucc < k := h
    simp [Fin.succAbove, hlt, h]
  · have hlt : ¬ u.castSucc < k := h
    simp [Fin.succAbove, hlt, h]

theorem shiftDown_succAbove {n : ℕ} (k : Fin (n + 1)) (u : Fin n) :
    shiftDown k.val (k.succAbove u).val = u.val := by
  rw [succAbove_val]
  unfold shiftDown
  split_ifs <;> omega

theorem shiftDown_col {n : ℕ} (k : Fin (n + 1)) (v : ℕ) :
    shiftDown k.val (n + 1 + v) = n + v := by
  unfold shiftDown
  have hk := k.isLt
  split_ifs <;> omega

theorem eq_succAbove_of_shiftDown {n : ℕ} (k : Fin (n + 1)) (u : Fin n) (i : ℕ)
    (hne : i ≠ k.val) (h : shiftDown k.val i = u.val) : i = (k.succAbove u).val := by
  rw [succAbove_val]
  unfold shiftDown at h
  split_ifs at h ⊢ <;> omega

theorem eq_col_of_shiftDown {n : ℕ} (k : Fin (n + 1)) (v : ℕ) (i : ℕ)
    (hne : i ≠ k.val) (h : shiftDown k.val i = n + v) : i = n + 1 + v := by
  have hk := k.isLt
  unfold shiftDown at h
  split_ifs at h <;> omega

theorem relFalse_oneEach {n m : ℕ} (k : Fin (n + 1)) (u : Fin n) (v : Fin m) :
    RelConst k.val false (oneEach (k.succAbove u) v) (oneEach u v) := by
  have hk := k.isLt
  refine ⟨by simp [oneEach_length]; omega, by rw [oneEach_length]; omega, ?_, ?_⟩
  · rw [oneEach_getD_left (k.succAbove u) v k.val hk]
    have hne : (k.succAbove u).val ≠ k.val := by
      rw [succAbove_val]
      split_ifs <;> omega
    simp [Ne.symm hne]
  · intro i hne
    by_cases h1 : i < n + 1
    · rw [oneEach_getD_left (k.succAbove u) v i h1]
      have hsh : shiftDown k.val i < n := by unfold shiftDown; split_ifs <;> omega
      rw [oneEach_getD_left u v (shiftDown k.val i) hsh]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · exact eq_succAbove_of_shiftDown k u i hne
      · intro heq
        rw [heq, shiftDown_succAbove]
    · by_cases h2 : i < n + 1 + m
      · rw [oneEach_getD_right (k.succAbove u) v i (by omega) h2]
        have hsh : shiftDown k.val i = i - 1 := by unfold shiftDown; split_ifs <;> omega
        rw [hsh, oneEach_getD_right u v (i - 1) (by omega) (by omega)]
        have heq : i - 1 - n = i - (n + 1) := by omega
        rw [heq]
      · have hsh : shiftDown k.val i = i - 1 := by unfold shiftDown; split_ifs <;> omega
        rw [hsh, getD_oob (oneEach u v) (i - 1) (by rw [oneEach_length]; omega),
          getD_oob (oneEach (k.succAbove u) v) i (by rw [oneEach_length]; omega)]

def restrictFalse (kval : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (substFalseGate kval), shiftDown kval C.output⟩

theorem restrictFalse_size (kval : ℕ) (C : Circuit) :
    (restrictFalse kval C).size = C.size := by
  simp [Circuit.size, restrictFalse]

theorem restrictFalse_fanInTwoNot1 (kval : ℕ) (C : Circuit) (hF : FanInTwoNot1 C) :
    FanInTwoNot1 (restrictFalse kval C) := by
  intro g hg
  simp only [restrictFalse, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  exact fanInTwoNot1_substFalseGate kval g0 (hF g0 hg0)

theorem restrictFalse_gateAt (kval : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size) :
    gateAt (restrictFalse kval C) j = substFalseGate kval (gateAt C j) := by
  have hj' : j < (restrictFalse kval C).gates.length := by simp [restrictFalse]; exact hj
  rw [gateAt_eq_getElem _ j hj', gateAt_eq_getElem C j hj]
  simp only [restrictFalse, List.getElem_map]
  rfl

theorem restrictFalse_represents {n m : ℕ} {A : Fin (n + 1) → Fin m → Bool}
    (k : Fin (n + 1)) (C : Circuit) (hF : FanInTwoNot1 C) (hRep : Represents A C)
    (hout : C.output ≠ k.val) :
    Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) v) (restrictFalse k.val C) := by
  intro u v
  dsimp only
  unfold Circuit.eval
  rw [wires_eq_foldl, ← hRep (k.succAbove u) v]
  unfold Circuit.eval
  rw [wires_eq_foldl]
  have hrel := relFalse_fold k.val C.gates hF _ _ (relFalse_oneEach k u v)
  exact hrel.2.2.2 C.output hout

theorem restrictFalse_listed_row {n : ℕ} (k : Fin (n + 1)) (C : Circuit) (hF : FanInTwoNot1 C)
    (hout : C.output ≠ k.val) (u : Fin n) (hL : Listed (restrictFalse k.val C) u.val) :
    Listed C (k.succAbove u).val := by
  rcases hL with ⟨g, hg, hwg⟩ | ho
  · simp only [restrictFalse, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨i, hi, hne, hsh⟩ := substFalseGate_mem k.val g0 (hF g0 hg0) hwg
    have heq := eq_succAbove_of_shiftDown k u i hne hsh.symm
    exact Or.inl ⟨g0, hg0, heq ▸ hi⟩
  · simp only [restrictFalse] at ho
    exact Or.inr (eq_succAbove_of_shiftDown k u C.output hout ho)

theorem restrictFalse_listed_col {n m : ℕ} (k : Fin (n + 1)) (C : Circuit) (hF : FanInTwoNot1 C)
    (hout : C.output ≠ k.val) (v : Fin m) (hL : Listed (restrictFalse k.val C) (n + v.val)) :
    Listed C (n + 1 + v.val) := by
  rcases hL with ⟨g, hg, hwg⟩ | ho
  · simp only [restrictFalse, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨i, hi, hne, hsh⟩ := substFalseGate_mem k.val g0 (hF g0 hg0) hwg
    have heq := eq_col_of_shiftDown k v.val i hne hsh.symm
    exact Or.inl ⟨g0, hg0, heq ▸ hi⟩
  · simp only [restrictFalse] at ho
    exact Or.inr (eq_col_of_shiftDown k v.val C.output hout ho)

theorem gateAt_delCopy_lt (N j y : ℕ) (C : Circuit) (r : ℕ) (hr : r < j) (hj : j < C.size) :
    gateAt (delCopy N j y C) r = gateAt C r := by
  simp only [Circuit.size] at hj
  have hr' : r < (delCopy N j y C).gates.length := by
    have := delCopy_size N j y C hj
    simp only [Circuit.size] at this
    omega
  rw [gateAt_eq_getElem _ r hr', gateAt_eq_getElem C r (by omega)]
  simp only [delCopy]
  rw [List.getElem_append_left (by simp; omega)]
  simp

theorem gateAt_delCopy_gt (N j y : ℕ) (C : Circuit) (r : ℕ) (hr1 : j < r) (hr2 : r < C.size) :
    gateAt (delCopy N j y C) (r - 1) = rd (N + j) y (gateAt C r) := by
  simp only [Circuit.size] at hr2
  have hj : j < C.size := by simp only [Circuit.size]; omega
  have hr' : r - 1 < (delCopy N j y C).gates.length := by
    have := delCopy_size N j y C hj
    simp only [Circuit.size] at this
    omega
  rw [gateAt_eq_getElem _ (r - 1) hr', gateAt_eq_getElem C r hr2]
  simp only [delCopy]
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem_map, List.getElem_drop]
  have hidx : j + 1 + (r - 1 - min j C.gates.length) = r := by omega
  simp only [hidx]

theorem gateAt_delConstTrue_gt (N j : ℕ) (C : Circuit) (r : ℕ) (hr1 : j < r) (hr2 : r < C.size) :
    gateAt (delConstTrue N j C) (r - 1) = substTrueGate (N + j) (gateAt C r) := by
  simp only [Circuit.size] at hr2
  have hj : j < C.size := by simp only [Circuit.size]; omega
  have hr' : r - 1 < (delConstTrue N j C).gates.length := by
    have := delConstTrue_size N j C hj
    simp only [Circuit.size] at this
    omega
  rw [gateAt_eq_getElem _ (r - 1) hr', gateAt_eq_getElem C r hr2]
  simp only [delConstTrue]
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem_map, List.getElem_drop]
  have hidx : j + 1 + (r - 1 - min j C.gates.length) = r := by omega
  simp only [hidx]

theorem gateAt_delConstFalse_gt (N j : ℕ) (C : Circuit) (r : ℕ) (hr1 : j < r) (hr2 : r < C.size) :
    gateAt (delConstFalse N j C) (r - 1) = substFalseGate (N + j) (gateAt C r) := by
  simp only [Circuit.size] at hr2
  have hj : j < C.size := by simp only [Circuit.size]; omega
  have hr' : r - 1 < (delConstFalse N j C).gates.length := by
    have := delConstFalse_size N j C hj
    simp only [Circuit.size] at this
    omega
  rw [gateAt_eq_getElem _ (r - 1) hr', gateAt_eq_getElem C r hr2]
  simp only [delConstFalse]
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem_map, List.getElem_drop]
  have hidx : j + 1 + (r - 1 - min j C.gates.length) = r := by omega
  simp only [hidx]

theorem finish_const_gate {n m : ℕ} {A : Fin (n + 1) → Fin m → Bool} (k : Fin (n + 1))
    (C : Circuit) (hRed : Reduced (n + 1 + m) C) (hRep : Represents A C)
    (hNC : NonConst (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) v))
    (hRB : ReadsBack (n + 1 + m) C)
    (hOut : C.output + 1 = (n + 1 + m) + C.size)
    (hReads : ∀ j < C.size, readsIn C (Finset.range C.size) ((n + 1 + m) + j) = 0 ↔ j + 1 = C.size)
    (j0 : ℕ) (hj0 : j0 < C.size) (b : Bool)
    (hb : (b = true ∧ gateAt (restrictFalse k.val C) j0 = ⟨GateOp.and, []⟩) ∨
          (b = false ∧ gateAt (restrictFalse k.val C) j0 = ⟨GateOp.or, []⟩)) :
    ∃ C2 : Circuit,
      FanInTwo C2 ∧
      Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) v) C2 ∧
      Reduced (n + m) C2 ∧
      C2.size + 1 ≤ C.size ∧
      (∀ u : Fin n, Listed C2 u.val → Listed C (k.succAbove u).val) ∧
      (∀ v : Fin m, Listed C2 (n + v.val) → Listed C (n + 1 + v.val)) ∧
      (C2.size + 2 ≤ C.size ∨ ∀ v : Fin m, Listed C (n + 1 + v.val) → Listed C2 (n + v.val)) := by
  set A' : Fin n → Fin m → Bool := fun u v => A (k.succAbove u) v
  have hFC : FanInTwoNot1 C := fanInTwoNot1_of_reduced hRed
  have hk : k.val < n + 1 := k.isLt
  have houtK : C.output ≠ k.val := by omega
  set C0 := restrictFalse k.val C with hC0def
  have hF0 : FanInTwoNot1 C0 := restrictFalse_fanInTwoNot1 k.val C hFC
  have hRep0 : Represents A' C0 := restrictFalse_represents k C hFC hRep houtK
  have hSz0 : C0.size = C.size := restrictFalse_size k.val C
  have hj0' : j0 < C0.size := by omega
  have hval0 : ∀ x : List Bool, x.length = n + m → (C0.wires x).getD (n + m + j0) false = b := by
    intro x hx
    rw [← hx, wires_gate_val C0 j0 hj0' x]
    rcases hb with ⟨rfl, hg0⟩ | ⟨rfl, hg0⟩ <;> simp [hg0, GateOp.eval]
  have hout0 : C0.output ≠ n + m + j0 := output_ne_of_const_gate hNC hRep0 j0 b hval0
  have hC0out : C0.output = n + m + C.size - 1 := by
    simp only [C0, restrictFalse, shiftDown]
    split_ifs <;> omega
  have hj0_lt : j0 + 1 < C.size := by omega
  have hnr : readsIn C (Finset.range C.size) ((n + 1 + m) + j0) ≠ 0 := by
    intro hz
    exact Nat.ne_of_lt hj0_lt ((hReads j0 hj0).mp hz)
  have hex : ∃ j1 < C.size, (n + 1 + m) + j0 ∈ (gateAt C j1).inputs := by
    by_contra hall
    push Not at hall
    exact hnr ((readsIn_range_eq_zero_iff C ((n + 1 + m) + j0)).mpr hall)
  obtain ⟨j1, hj1, hj1mem⟩ := hex
  have hj01 : j0 < j1 := by
    have := hRB j1 hj1 _ hj1mem
    omega
  have hj1_0 : j1 < C0.gates.length := by
    change j1 < C0.size
    omega
  have hC1_ex : ∃ C1 : Circuit,
      FanInTwoNot1 C1 ∧
      Represents A' C1 ∧
      C1.size + 1 = C.size ∧
      (∀ w < n + m, Listed C1 w → Listed C0 w) ∧
      ¬ Reduced (n + m) C1 := by
    rcases hb with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · refine ⟨delConstTrue (n + m) j0 C0, delConstTrue_fanInTwoNot1 (n + m) j0 C0 hF0, ?_,
        by rw [delConstTrue_size (n + m) j0 C0 hj0', hSz0],
        fun w hw => delConstTrue_listed (n + m) j0 C0 hF0 hout0 w hw, ?_⟩
      · intro u v
        rw [delConstTrue_eval (n + m) j0 C0 hF0 hj0' hout0 (oneEach u v) (oneEach_length u v)
          (hval0 _ (oneEach_length u v))]
        exact hRep0 u v
      · intro hRed1
        have hSz1 : (delConstTrue (n + m) j0 C0).size + 1 = C.size := by
          rw [delConstTrue_size (n + m) j0 C0 hj0', hSz0]
        rcases hRed1 with ⟨hGood1, _, _, _, _⟩ | ⟨h0, _⟩
        · have hj1' : j1 - 1 < (delConstTrue (n + m) j0 C0).size := by omega
          have hG1 : IsGoodGate (gateAt (delConstTrue (n + m) j0 C0) (j1 - 1)) :=
            hGood1 _ (gateAt_mem _ _ hj1')
          rw [gateAt_delConstTrue_gt (n + m) j0 C0 j1 hj01 (by omega)] at hG1
          by_cases hk1 : k.val ∈ (gateAt C j1).inputs
          · have hng0 : ¬ IsGoodGate (gateAt C0 j1) := by
              rw [restrictFalse_gateAt k.val C j1 hj1]
              exact not_isGoodGate_substFalseGate_of_mem k.val _ (hFC _ (gateAt_mem C j1 hj1)) hk1
            exact not_isGoodGate_substTrueGate_of_not_good (n + m + j0) _
              (hF0 _ (gateAt_mem C0 j1 hj1_0)) hng0 hG1
          · have hmem0 : n + m + j0 ∈ (gateAt C0 j1).inputs := by
              rw [restrictFalse_gateAt k.val C j1 hj1]
              have hsh : shiftDown k.val ((n + 1 + m) + j0) = n + m + j0 := by
                unfold shiftDown; split_ifs <;> omega
              rw [← hsh]
              exact substFalseGate_mem_of_not_mem k.val _ (hFC _ (gateAt_mem C j1 hj1)) hk1 hj1mem
            exact not_isGoodGate_substTrueGate_of_mem (n + m + j0) _
              (hF0 _ (gateAt_mem C0 j1 hj1_0)) hmem0 hG1
        · omega
    · refine ⟨delConstFalse (n + m) j0 C0, delConstFalse_fanInTwoNot1 (n + m) j0 C0 hF0, ?_,
        by rw [delConstFalse_size (n + m) j0 C0 hj0', hSz0],
        fun w hw => delConstFalse_listed (n + m) j0 C0 hF0 hout0 w hw, ?_⟩
      · intro u v
        rw [delConstFalse_eval (n + m) j0 C0 hF0 hj0' hout0 (oneEach u v) (oneEach_length u v)
          (hval0 _ (oneEach_length u v))]
        exact hRep0 u v
      · intro hRed1
        have hSz1 : (delConstFalse (n + m) j0 C0).size + 1 = C.size := by
          rw [delConstFalse_size (n + m) j0 C0 hj0', hSz0]
        rcases hRed1 with ⟨hGood1, _, _, _, _⟩ | ⟨h0, _⟩
        · have hj1' : j1 - 1 < (delConstFalse (n + m) j0 C0).size := by omega
          have hG1 : IsGoodGate (gateAt (delConstFalse (n + m) j0 C0) (j1 - 1)) :=
            hGood1 _ (gateAt_mem _ _ hj1')
          rw [gateAt_delConstFalse_gt (n + m) j0 C0 j1 hj01 (by omega)] at hG1
          by_cases hk1 : k.val ∈ (gateAt C j1).inputs
          · have hng0 : ¬ IsGoodGate (gateAt C0 j1) := by
              rw [restrictFalse_gateAt k.val C j1 hj1]
              exact not_isGoodGate_substFalseGate_of_mem k.val _ (hFC _ (gateAt_mem C j1 hj1)) hk1
            exact not_isGoodGate_substFalseGate_of_not_good (n + m + j0) _
              (hF0 _ (gateAt_mem C0 j1 hj1_0)) hng0 hG1
          · have hmem0 : n + m + j0 ∈ (gateAt C0 j1).inputs := by
              rw [restrictFalse_gateAt k.val C j1 hj1]
              have hsh : shiftDown k.val ((n + 1 + m) + j0) = n + m + j0 := by
                unfold shiftDown; split_ifs <;> omega
              rw [← hsh]
              exact substFalseGate_mem_of_not_mem k.val _ (hFC _ (gateAt_mem C j1 hj1)) hk1 hj1mem
            exact not_isGoodGate_substFalseGate_of_mem (n + m + j0) _
              (hF0 _ (gateAt_mem C0 j1 hj1_0)) hmem0 hG1
        · omega
  obtain ⟨C1, hF1, hRep1, hSz1, hL1, hNR1⟩ := hC1_ex
  obtain ⟨C2, hRed2, hRep2, hSz2, hL2, hDrop⟩ := reduce_circuit hNC C1.size C1 le_rfl hF1 hRep1
  have hSzDrop : C2.size + 1 ≤ C1.size := by
    rcases hDrop with h1 | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 hNR1
  refine ⟨C2, fanInTwo_of_reduced hRed2, hRep2, hRed2, by omega, ?_, ?_, Or.inl (by omega)⟩
  · intro u hu
    exact restrictFalse_listed_row k C hFC houtK u (hL1 u.val (by omega) (hL2 u.val (by omega) hu))
  · intro v hv
    exact restrictFalse_listed_col k C hFC houtK v
      (hL1 (n + v.val) (by omega) (hL2 (n + v.val) (by omega) hv))

theorem main :
    ∀ (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (k : Fin (n + 1)) (C : Circuit),
      FanInTwo C →
      Represents A C →
      Reduced (n + 1 + m) C →
      Listed C k.val →
      NonConst (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) v) →
      ∃ C2 : Circuit,
        FanInTwo C2 ∧
        Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) v) C2 ∧
        Reduced (n + m) C2 ∧
        C2.size + 1 ≤ C.size ∧
        (∀ u : Fin n, Listed C2 u.val → Listed C (k.succAbove u).val) ∧
        (∀ v : Fin m, Listed C2 (n + v.val) → Listed C (n + 1 + v.val)) ∧
        (C2.size + 2 ≤ C.size ∨ ∀ v : Fin m, Listed C (n + 1 + v.val) → Listed C2 (n + v.val)) := by
  intro n m A k C _ hRep hRed hListK hNC
  set A' : Fin n → Fin m → Bool := fun u v => A (k.succAbove u) v
  have hk : k.val < n + 1 := k.isLt
  rcases hRed with ⟨hGood, hRB, hPos, hOut, hReads⟩ | ⟨h0, hOut0⟩
  · have hRedFull : Reduced (n + 1 + m) C := Or.inl ⟨hGood, hRB, hPos, hOut, hReads⟩
    have hFC : FanInTwoNot1 C := fanInTwoNot1_of_reduced hRedFull
    have houtK : C.output ≠ k.val := by omega
    have hExGate : ∃ j0 < C.size, k.val ∈ (gateAt C j0).inputs := by
      rcases hListK with ⟨g, hg, hkg⟩ | ho
      · obtain ⟨j0, hj0, hgj0⟩ := (mem_gates_iff_gateAt C g).mp hg
        exact ⟨j0, hj0, hgj0.symm ▸ hkg⟩
      · exact absurd ho houtK
    obtain ⟨j0, hj0, hj0k⟩ := hExGate
    set C0 := restrictFalse k.val C with hC0def
    have hF0 : FanInTwoNot1 C0 := restrictFalse_fanInTwoNot1 k.val C hFC
    have hRep0 : Represents A' C0 := restrictFalse_represents k C hFC hRep houtK
    have hSz0 : C0.size = C.size := restrictFalse_size k.val C
    have hj0' : j0 < C0.size := by omega
    have hGj0 : IsGoodGate (gateAt C j0) := hGood _ (gateAt_mem C j0 hj0)
    rcases hGj0 with ⟨hop | hop, hlen⟩ | ⟨hop, hlen⟩
    · have hg0 : gateAt C0 j0 = ⟨GateOp.or, []⟩ := by
        rw [restrictFalse_gateAt k.val C j0 hj0]
        simp [substFalseGate, hop, hj0k]
      exact finish_const_gate k C hRedFull hRep hNC hRB hOut hReads j0 hj0 false
        (Or.inr ⟨rfl, hg0⟩)
    · cases hins : (gateAt C j0).inputs with
      | nil => rw [hins] at hlen; simp at hlen
      | cons a t =>
        cases t with
        | nil => rw [hins] at hlen; simp at hlen
        | cons b t2 =>
          cases t2 with
          | nil =>
            rw [hins] at hj0k
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj0k
            by_cases hab : a = k.val ∧ b = k.val
            · have hg0 : gateAt C0 j0 = ⟨GateOp.or, []⟩ := by
                rw [restrictFalse_gateAt k.val C j0 hj0]
                simp [substFalseGate, hop, hins, hab.1, hab.2]
              exact finish_const_gate k C hRedFull hRep hNC hRB hOut hReads j0 hj0 false
                (Or.inr ⟨rfl, hg0⟩)
            · have hx_ex : ∃ x : ℕ, x ≠ k.val ∧ x ∈ (gateAt C j0).inputs ∧
                  gateAt C0 j0 = ⟨GateOp.or, [shiftDown k.val x]⟩ ∧
                  ∀ z ∈ (gateAt C j0).inputs, z ≠ k.val → z = x := by
                rcases hj0k with hka | hkb
                · have hbk : b ≠ k.val := fun h => hab ⟨hka.symm, h⟩
                  refine ⟨b, hbk, by simp [hins], ?_, ?_⟩
                  · rw [restrictFalse_gateAt k.val C j0 hj0]
                    simp [substFalseGate, hop, hins, hka.symm, hbk]
                  · intro z hz hne
                    rw [hins] at hz
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                    rcases hz with rfl | rfl
                    · exact absurd hka.symm hne
                    · rfl
                · have hak : a ≠ k.val := fun h => hab ⟨h, hkb.symm⟩
                  refine ⟨a, hak, by simp [hins], ?_, ?_⟩
                  · rw [restrictFalse_gateAt k.val C j0 hj0]
                    simp [substFalseGate, hop, hins, hkb.symm, hak]
                  · intro z hz hne
                    rw [hins] at hz
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                    rcases hz with rfl | rfl
                    · rfl
                    · exact absurd hkb.symm hne
              obtain ⟨x, hxk, hxin, hg0, hxuniq⟩ := hx_ex
              set x' := shiftDown k.val x with hx'def
              have hxlt : x < (n + 1 + m) + j0 := hRB j0 hj0 x hxin
              have hx'lt : x' < n + m + j0 := by
                unfold x' shiftDown
                split_ifs <;> omega
              have hcopy : ∀ w : List Bool, w.length = n + m →
                  (C0.wires w).getD (n + m + j0) false = (C0.wires w).getD x' false := by
                intro w hw
                rw [← hw, wires_gate_val C0 j0 hj0' w, wires_gate_lt C0 j0 hj0' w x' (by omega)]
                simp [hg0, GateOp.eval]
              set C1 := delCopy (n + m) j0 x' C0 with hC1def
              have hF1 : FanInTwoNot1 C1 := delCopy_fanInTwoNot1 (n + m) j0 x' C0 hF0
              have hSz1 : C1.size + 1 = C.size := by
                rw [delCopy_size (n + m) j0 x' C0 hj0', hSz0]
              have hRep1 : Represents A' C1 := by
                intro u v
                rw [delCopy_eval (n + m) j0 x' C0 hj0' hx'lt (oneEach u v) (oneEach_length u v)
                  (hcopy _ (oneEach_length u v))]
                exact hRep0 u v
              have hL1 : ∀ w < n + m, Listed C1 w → Listed C0 w :=
                fun w hw => delCopy_listed (n + m) j0 x' C0 hj0' (by simp [hg0]) w hw
              obtain ⟨C2, hRed2, hRep2, hSz2, hL2, hDrop⟩ :=
                reduce_circuit hNC C1.size C1 le_rfl hF1 hRep1
              refine ⟨C2, fanInTwo_of_reduced hRed2, hRep2, hRed2, by omega, ?_, ?_, ?_⟩
              · intro u hu
                exact restrictFalse_listed_row k C hFC houtK u
                  (hL1 u.val (by omega) (hL2 u.val (by omega) hu))
              · intro v hv
                exact restrictFalse_listed_col k C hFC houtK v
                  (hL1 (n + v.val) (by omega) (hL2 (n + v.val) (by omega) hv))
              · rcases hDrop with hStrict | ⟨hRed1, hSurv12⟩
                · exact Or.inl (by omega)
                · right
                  intro v hv
                  apply hSurv12 (n + v.val) (by omega)
                  have hUniqK : ∀ j < C.size, j ≠ j0 → k.val ∉ (gateAt C j).inputs := by
                    intro j hj hne hkj
                    rcases hRed1 with ⟨hGood1, _, _, _, _⟩ | ⟨h01, _⟩
                    · have hng0 : ¬ IsGoodGate (gateAt C0 j) := by
                        rw [restrictFalse_gateAt k.val C j hj]
                        exact not_isGoodGate_substFalseGate_of_mem k.val _
                          (hFC _ (gateAt_mem C j hj)) hkj
                      by_cases hltj : j < j0
                      · have hj' : j < C1.size := by omega
                        have hG1 := hGood1 _ (gateAt_mem C1 j hj')
                        rw [gateAt_delCopy_lt (n + m) j0 x' C0 j hltj hj0'] at hG1
                        exact hng0 hG1
                      · have hgtj : j0 < j := by omega
                        have hj' : j - 1 < C1.size := by omega
                        have hG1 := hGood1 _ (gateAt_mem C1 (j - 1) hj')
                        rw [gateAt_delCopy_gt (n + m) j0 x' C0 j hgtj (by omega)] at hG1
                        exact hng0 (by simpa [IsGoodGate, rd] using hG1)
                    · omega
                  have hvOut : C.output ≠ n + 1 + v.val := by have := v.isLt; omega
                  rcases hv with ⟨g, hg, hvg⟩ | ho
                  · obtain ⟨j, hj, hgj⟩ := (mem_gates_iff_gateAt C g).mp hg
                    rw [← hgj] at hvg
                    by_cases hjj0 : j = j0
                    · subst j
                      have hxe : n + 1 + v.val = x := hxuniq _ hvg (by omega)
                      have hx'v : x' = n + v.val := by
                        rw [hx'def, ← hxe, shiftDown_col]
                      by_cases hlast : j0 + 1 = C.size
                      · right
                        have hC0o : C0.output = n + m + j0 := by
                          simp only [C0, restrictFalse, shiftDown]
                          split_ifs <;> omega
                        simp only [C1, delCopy, hC0o, sig, hx'v]
                        simp
                      · have hnr0 : readsIn C (Finset.range C.size) ((n + 1 + m) + j0) ≠ 0 := by
                          intro hz
                          exact hlast ((hReads j0 hj0).mp hz)
                        have hex1 : ∃ j1 < C.size, (n + 1 + m) + j0 ∈ (gateAt C j1).inputs := by
                          by_contra hall
                          push Not at hall
                          exact hnr0 ((readsIn_range_eq_zero_iff C ((n + 1 + m) + j0)).mpr hall)
                        obtain ⟨j1, hj1, hj1m⟩ := hex1
                        have hj01 : j0 < j1 := by
                          have := hRB j1 hj1 _ hj1m
                          omega
                        have hnk1 : k.val ∉ (gateAt C j1).inputs := hUniqK j1 hj1 (by omega)
                        have hmem0 : n + m + j0 ∈ (gateAt C0 j1).inputs := by
                          rw [restrictFalse_gateAt k.val C j1 hj1]
                          have hsh : shiftDown k.val ((n + 1 + m) + j0) = n + m + j0 := by
                            unfold shiftDown; split_ifs <;> omega
                          rw [← hsh]
                          exact substFalseGate_mem_of_not_mem k.val _
                            (hFC _ (gateAt_mem C j1 hj1)) hnk1 hj1m
                        left
                        have hj1' : j1 - 1 < C1.size := by omega
                        refine ⟨gateAt C1 (j1 - 1), gateAt_mem C1 (j1 - 1) hj1', ?_⟩
                        rw [gateAt_delCopy_gt (n + m) j0 x' C0 j1 hj01 (by omega)]
                        simp only [rd, List.mem_map]
                        refine ⟨n + m + j0, hmem0, ?_⟩
                        simp [sig, hx'v]
                    · have hnk : k.val ∉ (gateAt C j).inputs := hUniqK j hj hjj0
                      have hmem0 : n + v.val ∈ (gateAt C0 j).inputs := by
                        rw [restrictFalse_gateAt k.val C j hj]
                        rw [← shiftDown_col k v.val]
                        exact substFalseGate_mem_of_not_mem k.val _
                          (hFC _ (gateAt_mem C j hj)) hnk hvg
                      left
                      by_cases hltj : j < j0
                      · have hj' : j < C1.size := by omega
                        refine ⟨gateAt C1 j, gateAt_mem C1 j hj', ?_⟩
                        rw [gateAt_delCopy_lt (n + m) j0 x' C0 j hltj hj0']
                        exact hmem0
                      · have hgtj : j0 < j := by omega
                        have hj' : j - 1 < C1.size := by omega
                        refine ⟨gateAt C1 (j - 1), gateAt_mem C1 (j - 1) hj', ?_⟩
                        rw [gateAt_delCopy_gt (n + m) j0 x' C0 j hgtj (by omega)]
                        simp only [rd, List.mem_map]
                        refine ⟨n + v.val, hmem0, ?_⟩
                        have hvlt := v.isLt
                        unfold sig
                        split_ifs <;> omega
                  · exact absurd ho hvOut
          | cons _ _ => rw [hins] at hlen; simp at hlen
    · cases hins : (gateAt C j0).inputs with
      | nil => rw [hins] at hlen; simp at hlen
      | cons a t =>
        cases t with
        | nil =>
          rw [hins, List.mem_singleton] at hj0k
          subst hj0k
          have hg0 : gateAt C0 j0 = ⟨GateOp.and, []⟩ := by
            rw [restrictFalse_gateAt k.val C j0 hj0]
            simp [substFalseGate, hop, hins]
          exact finish_const_gate k C hRedFull hRep hNC hRB hOut hReads j0 hj0 true
            (Or.inl ⟨rfl, hg0⟩)
        | cons _ _ => rw [hins] at hlen; simp at hlen
  · exfalso
    have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero h0
    have hok : C.output = k.val := by
      rcases hListK with ⟨g, hg, _⟩ | ho
      · rw [hnil] at hg; cases hg
      · exact ho
    obtain ⟨u, u2, v, v2, hne⟩ := hNC
    have hev : ∀ (u0 : Fin n) (v0 : Fin m), A (k.succAbove u0) v0 = false := by
      intro u0 v0
      rw [← hRep (k.succAbove u0) v0]
      unfold Circuit.eval
      rw [wires_eq_foldl, hnil, List.foldl_nil, hok, oneEach_getD_left (k.succAbove u0) v0 k.val hk]
      have hne' : (k.succAbove u0).val ≠ k.val := by
        rw [succAbove_val]
        split_ifs <;> omega
      simp [Ne.symm hne']
    exact hne ((hev u v).trans (hev u2 v2).symm)

end PEqualNP.Outside.L_meta_24694

theorem PEqualNP.Outside.L_meta_24694 : (∀ (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (k : Fin (n + 1)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ((∀ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 1 + m) C ∧ 0 < C.size ∧ C.output + 1 = (n + 1 + m) + C.size ∧ (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) ((n + 1 + m) + j) = 0 ↔ j + 1 = C.size)) ∨ (C.size = 0 ∧ C.output < (n + 1 + m))) → ((∃ g ∈ C.gates, k.val ∈ g.inputs) ∨ C.output = k.val) → (∃ (u u2 : Fin n) (v v2 : Fin m), A (k.succAbove u) v ≠ A (k.succAbove u2) v2) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => A (k.succAbove u) v) C2 ∧ ((∀ g ∈ C2.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C2 ∧ 0 < C2.size ∧ C2.output + 1 = (n + m) + C2.size ∧ (∀ j < C2.size, (PEqualNP.MetaComplexity.NestedCover.readsIn C2 (Finset.range C2.size) ((n + m) + j) = 0 ↔ j + 1 = C2.size)) ∨ (C2.size = 0 ∧ C2.output < (n + m))) ∧ C2.size + 1 ≤ C.size ∧ (∀ u : Fin n, ((∃ g ∈ C2.gates, u.val ∈ g.inputs) ∨ C2.output = u.val) → ((∃ g ∈ C.gates, (k.succAbove u).val ∈ g.inputs) ∨ C.output = (k.succAbove u).val)) ∧ (∀ v : Fin m, ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)) → ((∃ g ∈ C.gates, (n + 1 + v.val) ∈ g.inputs) ∨ C.output = (n + 1 + v.val))) ∧ (C2.size + 2 ≤ C.size ∨ ∀ v : Fin m, ((∃ g ∈ C.gates, (n + 1 + v.val) ∈ g.inputs) ∨ C.output = (n + 1 + v.val)) → ((∃ g ∈ C2.gates, (n + v.val) ∈ g.inputs) ∨ C2.output = (n + v.val)))) := by
  exact PEqualNP.Outside.L_meta_24694.main
