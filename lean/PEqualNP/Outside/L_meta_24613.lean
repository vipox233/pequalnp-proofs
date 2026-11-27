import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24613

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def stripGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

def stripNot (C : Circuit) : Circuit :=
  ⟨C.gates.map stripGate, C.output⟩

def NotLeOne (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1

def UsesWire (C : Circuit) (w : ℕ) : Prop :=
  (∃ g ∈ C.gates, w ∈ g.inputs) ∨ C.output = w

def EffUsesWire (C : Circuit) (w : ℕ) : Prop :=
  (∃ g ∈ C.gates,
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ w ∈ g.inputs) ∨
    (g.op = GateOp.not ∧ g.inputs.head? = some w)) ∨
  C.output = w

def StrictShape (C : Circuit) : Prop :=
  ∀ g ∈ C.gates,
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1)

def Reduced (N : ℕ) (D : Circuit) : Prop :=
  StrictShape D ∧
  ReadsBack N D ∧
  0 < D.size ∧
  D.output + 1 = N + D.size ∧
  (∀ j < D.size, (readsIn D (Finset.range D.size) (N + j) = 0 ↔ j + 1 = D.size))

def shiftDown (k i : ℕ) : ℕ :=
  if i < k then i else i - 1

def remapCopy (k a i : ℕ) : ℕ :=
  if i < k then i
  else if i = k then a
  else i - 1

def mapGate (f : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map f⟩

def substConstGate (k : ℕ) (b : Bool) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and =>
    if !b && k ∈ g.inputs then ⟨GateOp.or, []⟩
    else ⟨GateOp.and, (g.inputs.filter (· ≠ k)).map (shiftDown k)⟩
  | GateOp.or =>
    if b && k ∈ g.inputs then ⟨GateOp.and, []⟩
    else ⟨GateOp.or, (g.inputs.filter (· ≠ k)).map (shiftDown k)⟩
  | GateOp.not =>
    match g.inputs with
    | [] => ⟨GateOp.and, []⟩
    | a :: _ =>
      if a = k then (if b then ⟨GateOp.or, []⟩ else ⟨GateOp.and, []⟩)
      else ⟨GateOp.not, [shiftDown k a]⟩
  | _ => g

lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_right {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

lemma getD_of_le_length {α : Type*} (l : List α) (i : ℕ) (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma getD_lt_mid (W₀ R : List Bool) (v : Bool) (i : ℕ) (h : i < W₀.length) :
    (W₀ ++ [v] ++ R).getD i false = (W₀ ++ R).getD i false := by
  rw [List.append_assoc, getD_append_left W₀ ([v] ++ R) i false h, getD_append_left W₀ R i false h]

lemma getD_eq_mid (W₀ R : List Bool) (v : Bool) :
    (W₀ ++ [v] ++ R).getD W₀.length false = v := by
  rw [List.append_assoc, getD_append_right W₀ ([v] ++ R) W₀.length false (le_refl _)]
  simp

lemma getD_gt_mid (W₀ R : List Bool) (v : Bool) (i : ℕ) (h : W₀.length < i) :
    (W₀ ++ [v] ++ R).getD i false = (W₀ ++ R).getD (i - 1) false := by
  rw [List.append_assoc, getD_append_right W₀ ([v] ++ R) i false (Nat.le_of_lt h)]
  rw [getD_append_right W₀ R (i - 1) false (by omega)]
  have hsub : i - W₀.length = (i - 1 - W₀.length) + 1 := by omega
  rw [hsub]
  rfl

lemma getD_shiftDown (W₀ R : List Bool) (v : Bool) (i : ℕ) (hne : i ≠ W₀.length) :
    (W₀ ++ R).getD (shiftDown W₀.length i) false = (W₀ ++ [v] ++ R).getD i false := by
  unfold shiftDown
  by_cases hlt : i < W₀.length
  · simp only [hlt, ↓reduceIte]
    exact (getD_lt_mid W₀ R v i hlt).symm
  · have hgt : W₀.length < i := by omega
    simp only [hlt, ↓reduceIte]
    exact (getD_gt_mid W₀ R v i hgt).symm

lemma getD_remapCopy (W₀ R : List Bool) (a : ℕ) (ha : a < W₀.length) (i : ℕ) :
    (W₀ ++ R).getD (remapCopy W₀.length a i) false =
      (W₀ ++ [W₀.getD a false] ++ R).getD i false := by
  unfold remapCopy
  by_cases hlt : i < W₀.length
  · simp only [hlt, ↓reduceIte]
    exact (getD_lt_mid W₀ R (W₀.getD a false) i hlt).symm
  · simp only [hlt, ↓reduceIte]
    by_cases heq : i = W₀.length
    · subst heq
      simp only [↓reduceIte]
      rw [getD_eq_mid, getD_append_left W₀ R a false ha]
    · have hgt : W₀.length < i := by omega
      simp only [heq, ↓reduceIte]
      exact (getD_gt_mid W₀ R (W₀.getD a false) i hgt).symm

lemma foldl_gateStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl gateStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [gateStep]
    omega

lemma foldl_gateStep_prefix (gs : List Gate) (w : List Bool) :
    ∃ R : List Bool, gs.foldl gateStep w = w ++ R := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rcases ih (gateStep w g) with ⟨R, hR⟩
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: R, ?_⟩
    rw [hR]
    simp [gateStep]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl gateStep x := rfl

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size :=
  foldl_gateStep_length C.gates x

lemma wires_getD_lt (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  rcases foldl_gateStep_prefix C.gates x with ⟨R, hR⟩
  rw [wires_eq_foldl, hR, getD_append_left x R i false hi]

lemma eval_of_ge_size (C : Circuit) (x : List Bool) (h : x.length + C.size ≤ C.output) :
    C.eval x = false := by
  unfold Circuit.eval
  apply getD_of_le_length
  rw [wires_length]
  exact h

lemma list_split {α : Type*} (l : List α) (j : ℕ) (hj : j < l.length) :
    l = l.take j ++ [l[j]] ++ l.drop (j + 1) := by
  have h1 : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
  calc
    l = l.take j ++ l.drop j := h1
    _ = l.take j ++ (l[j] :: l.drop (j + 1)) := by rw [h2]
    _ = l.take j ++ [l[j]] ++ l.drop (j + 1) := by simp

lemma foldl_sim (W₀ : List Bool) (v : Bool) (after : List Gate) (f : Gate → Gate)
    (hstep : ∀ g ∈ after, ∀ R : List Bool,
      (f g).op.eval ((f g).inputs.map fun i => (W₀ ++ R).getD i false) =
        g.op.eval (g.inputs.map fun i => (W₀ ++ [v] ++ R).getD i false)) :
    ∀ R : List Bool, ∃ R' : List Bool,
      after.foldl gateStep (W₀ ++ [v] ++ R) = W₀ ++ [v] ++ (R ++ R') ∧
      (after.map f).foldl gateStep (W₀ ++ R) = W₀ ++ (R ++ R') := by
  induction after with
  | nil =>
    intro R
    exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro R
    have hg : (f g).op.eval ((f g).inputs.map fun i => (W₀ ++ R).getD i false) =
        g.op.eval (g.inputs.map fun i => (W₀ ++ [v] ++ R).getD i false) :=
      hstep g (by simp) R
    have hgs : ∀ g' ∈ gs, ∀ R' : List Bool,
        (f g').op.eval ((f g').inputs.map fun i => (W₀ ++ R').getD i false) =
          g'.op.eval (g'.inputs.map fun i => (W₀ ++ [v] ++ R').getD i false) :=
      fun g' hg' => hstep g' (by simp [hg'])
    set b := g.op.eval (g.inputs.map fun i => (W₀ ++ [v] ++ R).getD i false)
    rcases ih hgs (R ++ [b]) with ⟨R', h1, h2⟩
    refine ⟨b :: R', ?_, ?_⟩
    · simp only [List.foldl_cons]
      have hs : gateStep (W₀ ++ [v] ++ R) g = W₀ ++ [v] ++ (R ++ [b]) := by
        unfold gateStep
        rw [List.append_assoc]
      rw [hs, h1]
      simp [List.append_assoc]
    · simp only [List.map_cons, List.foldl_cons]
      have hs : gateStep (W₀ ++ R) (f g) = W₀ ++ (R ++ [b]) := by
        unfold gateStep
        rw [hg]
        rw [List.append_assoc]
      rw [hs, h2]
      simp [List.append_assoc]

lemma foldl_sim_nil (W₀ : List Bool) (v : Bool) (after : List Gate) (f : Gate → Gate)
    (hstep : ∀ g ∈ after, ∀ R : List Bool,
      (f g).op.eval ((f g).inputs.map fun i => (W₀ ++ R).getD i false) =
        g.op.eval (g.inputs.map fun i => (W₀ ++ [v] ++ R).getD i false)) :
    ∃ R : List Bool,
      after.foldl gateStep (W₀ ++ [v]) = W₀ ++ [v] ++ R ∧
      (after.map f).foldl gateStep W₀ = W₀ ++ R := by
  simpa using foldl_sim W₀ v after f hstep []

lemma gateStep_stripGate (w : List Bool) (g : Gate) :
    gateStep w (stripGate g) = gateStep w g := by
  cases g with
  | mk op ins =>
    unfold gateStep stripGate
    cases op with
    | not =>
      cases ins with
      | nil => rfl
      | cons a t => rfl
    | and => rfl
    | or => rfl
    | mod m => rfl
    | maj => rfl

lemma stripNot_wires (C : Circuit) (x : List Bool) :
    (stripNot C).wires x = C.wires x := by
  change (C.gates.map stripGate).foldl gateStep x = C.gates.foldl gateStep x
  generalize C.gates = gs
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, gateStep_stripGate]
    exact ih _

lemma stripNot_eval (C : Circuit) (x : List Bool) :
    (stripNot C).eval x = C.eval x := by
  unfold Circuit.eval
  rw [stripNot_wires]
  rfl

lemma stripNot_size (C : Circuit) : (stripNot C).size = C.size := by
  simp [Circuit.size, stripNot]

lemma mem_op_iff (op : GateOp) :
    op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ↔
      op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := by
  simp

lemma stripNot_fanInTwo (C : Circuit) (hF : FanInTwo C) : FanInTwo (stripNot C) := by
  intro g hg
  simp only [stripNot, List.mem_map] at hg
  rcases hg with ⟨g₀, hg₀, rfl⟩
  rcases hF g₀ hg₀ with ⟨hop, hlen⟩
  cases g₀ with
  | mk op ins =>
    unfold stripGate
    cases op with
    | not =>
      refine ⟨hop, ?_⟩
      simp only [List.length_take]
      omega
    | and => exact ⟨hop, hlen⟩
    | or => exact ⟨hop, hlen⟩
    | mod m => exact ⟨hop, hlen⟩
    | maj => exact ⟨hop, hlen⟩

lemma stripNot_notLeOne (C : Circuit) : NotLeOne (stripNot C) := by
  intro g hg hop
  simp only [stripNot, List.mem_map] at hg
  rcases hg with ⟨g₀, _, rfl⟩
  cases g₀ with
  | mk op ins =>
    unfold stripGate at hop ⊢
    cases op with
    | not => simp
    | and => cases hop
    | or => cases hop
    | mod m => cases hop
    | maj => cases hop

lemma mem_take_one_iff {α : Type*} (l : List α) (w : α) :
    w ∈ l.take 1 ↔ l.head? = some w := by
  cases l with
  | nil => simp
  | cons a t => simp [eq_comm]

lemma stripNot_usesWire_iff (C : Circuit) (hF : FanInTwo C) (w : ℕ) :
    UsesWire (stripNot C) w ↔ EffUsesWire C w := by
  unfold UsesWire EffUsesWire stripNot
  simp only [List.mem_map]
  constructor
  · rintro (⟨g, ⟨g₀, hg₀, rfl⟩, hw⟩ | hout)
    · left
      refine ⟨g₀, hg₀, ?_⟩
      have hop := (mem_op_iff g₀.op).mp (hF g₀ hg₀).1
      rcases hop with h1 | h2 | h3
      · left; exact ⟨Or.inl h1, by simpa [stripGate, h1] using hw⟩
      · left; exact ⟨Or.inr h2, by simpa [stripGate, h2] using hw⟩
      · right
        have hw' : w ∈ g₀.inputs.take 1 := by simpa [stripGate, h3] using hw
        exact ⟨h3, (mem_take_one_iff g₀.inputs w).mp hw'⟩
    · exact Or.inr hout
  · rintro (⟨g₀, hg₀, (⟨hor, hw⟩ | ⟨hnot, hhead⟩)⟩ | hout)
    · left
      refine ⟨stripGate g₀, ⟨g₀, hg₀, rfl⟩, ?_⟩
      rcases hor with h1 | h2
      · simpa [stripGate, h1] using hw
      · simpa [stripGate, h2] using hw
    · left
      refine ⟨stripGate g₀, ⟨g₀, hg₀, rfl⟩, ?_⟩
      simpa [stripGate, hnot, mem_take_one_iff] using hhead
    · exact Or.inr hout

lemma substConstGate_fanInTwo (k : ℕ) (b : Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    (substConstGate k b g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
    (substConstGate k b g).inputs.length ≤ 2 := by
  have hop' := (mem_op_iff g.op).mp hop
  unfold substConstGate
  rcases hop' with h1 | h2 | h3
  · rw [h1]
    dsimp only
    split_ifs
    · simp
    · refine ⟨by simp, ?_⟩
      simp only [List.length_map]
      exact Nat.le_trans (List.length_filter_le _ _) hlen
  · rw [h2]
    dsimp only
    split_ifs
    · simp
    · refine ⟨by simp, ?_⟩
      simp only [List.length_map]
      exact Nat.le_trans (List.length_filter_le _ _) hlen
  · rw [h3]
    dsimp only
    cases g.inputs with
    | nil => simp
    | cons a t =>
      dsimp only
      split_ifs <;> simp

lemma substConstGate_notLeOne (k : ℕ) (b : Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (substConstGate k b g).op = GateOp.not → (substConstGate k b g).inputs.length ≤ 1 := by
  have hop' := (mem_op_iff g.op).mp hop
  unfold substConstGate
  rcases hop' with h1 | h2 | h3
  · rw [h1]
    dsimp only
    split_ifs <;> simp
  · rw [h2]
    dsimp only
    split_ifs <;> simp
  · rw [h3]
    dsimp only
    cases g.inputs with
    | nil => simp
    | cons a t =>
      dsimp only
      split_ifs <;> simp

lemma substConstGate_eval (W₀ R : List Bool) (b : Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (substConstGate W₀.length b g).op.eval
        ((substConstGate W₀.length b g).inputs.map fun i => (W₀ ++ R).getD i false) =
      g.op.eval (g.inputs.map fun i => (W₀ ++ [b] ++ R).getD i false) := by
  have hop' := (mem_op_iff g.op).mp hop
  set k := W₀.length
  unfold substConstGate
  rcases hop' with h1 | h2 | h3
  · rw [h1]
    dsimp only
    by_cases hbf : !b && k ∈ g.inputs
    · simp only [hbf, ↓reduceIte]
      have hb : b = false := by cases b <;> simp_all
      have hk : k ∈ g.inputs := by cases b <;> simp_all
      subst hb
      change false = (g.inputs.map fun i => (W₀ ++ [false] ++ R).getD i false).all id
      symm
      rw [Bool.eq_false_iff]
      intro hall
      rw [List.all_eq_true] at hall
      have hmem : (W₀ ++ [false] ++ R).getD k false ∈
          g.inputs.map (fun i => (W₀ ++ [false] ++ R).getD i false) :=
        List.mem_map_of_mem hk
      have htrue := hall _ hmem
      simp only [id_eq] at htrue
      rw [getD_eq_mid] at htrue
      cases htrue
    · simp only [hbf]
      change (((g.inputs.filter (· ≠ k)).map (shiftDown k)).map
          fun i => (W₀ ++ R).getD i false).all id =
        (g.inputs.map fun i => (W₀ ++ [b] ++ R).getD i false).all id
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id_eq]
      constructor
      · intro h y hy
        rcases hy with ⟨i, hi, rfl⟩
        by_cases hik : i = k
        · subst hik
          rw [getD_eq_mid]
          cases b with
          | true => rfl
          | false =>
            exfalso
            apply hbf
            simp [hi]
        · rw [← getD_shiftDown W₀ R b i hik]
          exact h _ ⟨shiftDown k i, ⟨i, ⟨hi, hik⟩, rfl⟩, rfl⟩
      · intro h y hy
        rcases hy with ⟨j, ⟨i, ⟨hi, hik⟩, rfl⟩, rfl⟩
        rw [getD_shiftDown W₀ R b i hik]
        exact h _ ⟨i, hi, rfl⟩
  · rw [h2]
    dsimp only
    by_cases hbt : b && k ∈ g.inputs
    · simp only [hbt, ↓reduceIte]
      have hb : b = true := by cases b <;> simp_all
      have hk : k ∈ g.inputs := by cases b <;> simp_all
      subst hb
      change true = (g.inputs.map fun i => (W₀ ++ [true] ++ R).getD i false).any id
      symm
      rw [List.any_eq_true]
      refine ⟨(W₀ ++ [true] ++ R).getD k false, List.mem_map_of_mem hk, ?_⟩
      simp only [id_eq]
      exact getD_eq_mid W₀ R true
    · simp only [hbt]
      change (((g.inputs.filter (· ≠ k)).map (shiftDown k)).map
          fun i => (W₀ ++ R).getD i false).any id =
        (g.inputs.map fun i => (W₀ ++ [b] ++ R).getD i false).any id
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id_eq]
      constructor
      · rintro ⟨_, ⟨_, ⟨i, ⟨hi, hik⟩, rfl⟩, rfl⟩, ht⟩
        rw [getD_shiftDown W₀ R b i hik] at ht
        exact ⟨_, ⟨i, hi, rfl⟩, ht⟩
      · rintro ⟨_, ⟨i, hi, rfl⟩, ht⟩
        by_cases hik : i = k
        · subst hik
          rw [getD_eq_mid] at ht
          exfalso
          apply hbt
          simp [ht, hi]
        · refine ⟨(W₀ ++ R).getD (shiftDown k i) false,
            ⟨shiftDown k i, ⟨i, ⟨hi, hik⟩, rfl⟩, rfl⟩, ?_⟩
          rwa [getD_shiftDown W₀ R b i hik]
  · rw [h3]
    dsimp only
    cases hin : g.inputs with
    | nil => rfl
    | cons a t =>
      dsimp only
      by_cases hak : a = k
      · subst hak
        simp only [↓reduceIte]
        cases b with
        | true =>
          change false = (!((W₀ ++ [true] ++ R).getD k false))
          rw [getD_eq_mid]
          rfl
        | false =>
          change true = (!((W₀ ++ [false] ++ R).getD k false))
          rw [getD_eq_mid]
          rfl
      · simp only [hak, ↓reduceIte]
        change (!((W₀ ++ R).getD (shiftDown k a) false)) = (!((W₀ ++ [b] ++ R).getD a false))
        rw [getD_shiftDown W₀ R b a hak]

lemma substConstGate_mem_inputs {N k w : ℕ} (hNk : N ≤ k) (hw : w < N) (b : Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hmem : w ∈ (substConstGate k b g).inputs) :
    w ∈ g.inputs := by
  have hop' := (mem_op_iff g.op).mp hop
  unfold substConstGate at hmem
  rcases hop' with h1 | h2 | h3
  · rw [h1] at hmem
    dsimp only at hmem
    split_ifs at hmem
    · simp at hmem
    · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hmem
      rcases hmem with ⟨i, ⟨hi, hik⟩, hsh⟩
      unfold shiftDown at hsh
      split_ifs at hsh with hlt
      · rwa [← hsh]
      · omega
  · rw [h2] at hmem
    dsimp only at hmem
    split_ifs at hmem
    · simp at hmem
    · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hmem
      rcases hmem with ⟨i, ⟨hi, hik⟩, hsh⟩
      unfold shiftDown at hsh
      split_ifs at hsh with hlt
      · rwa [← hsh]
      · omega
  · rw [h3] at hmem
    dsimp only at hmem
    cases hin : g.inputs with
    | nil =>
      rw [hin] at hmem
      simp at hmem
    | cons a t =>
      rw [hin] at hmem
      dsimp only at hmem
      by_cases hak : a = k
      · simp only [hak, ↓reduceIte] at hmem
        cases b <;> simp at hmem
      · simp only [hak, ↓reduceIte] at hmem
        simp only [List.mem_singleton] at hmem
        unfold shiftDown at hmem
        split_ifs at hmem with hlt
        · subst hmem; simp
        · omega

lemma deleteConst (N : ℕ) (C : Circuit) (hF : FanInTwo C) (hN : NotLeOne C)
    (hNC : ∃ x y : List Bool, x.length = N ∧ y.length = N ∧ C.eval x ≠ C.eval y)
    (j : ℕ) (hj : j < C.gates.length) (b : Bool)
    (hb : ∀ W₀ : List Bool, W₀.length = N + j →
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => W₀.getD i false) = b) :
    ∃ C' : Circuit,
      FanInTwo C' ∧
      NotLeOne C' ∧
      C'.size + 1 = C.size ∧
      (∀ x : List Bool, x.length = N → C'.eval x = C.eval x) ∧
      (∀ w < N, UsesWire C' w → UsesWire C w) := by
  set k := N + j
  set before := C.gates.take j
  set gj := C.gates[j]
  set after := C.gates.drop (j + 1)
  have hsplit : C.gates = before ++ [gj] ++ after := list_split C.gates j hj
  have hblen : before.length = j := by simp [before, Nat.le_of_lt hj]
  have hout_ne : C.output ≠ k := by
    intro hout
    rcases hNC with ⟨x, y, hx, hy, hne⟩
    have eval_eq : ∀ z : List Bool, z.length = N → C.eval z = b := by
      intro z hz
      unfold Circuit.eval
      rw [wires_eq_foldl, hsplit, List.foldl_append, List.foldl_append]
      set W₀ := before.foldl gateStep z
      have hW₀len : W₀.length = k := by
        rw [foldl_gateStep_length, hz, hblen]
      have hstepj : [gj].foldl gateStep W₀ = W₀ ++ [b] := by
        simp only [List.foldl_cons, List.foldl_nil, gateStep, gj]
        rw [hb W₀ hW₀len]
      rw [hstepj]
      rcases foldl_gateStep_prefix after (W₀ ++ [b]) with ⟨R, hR⟩
      rw [hR, hout, ← hW₀len]
      exact getD_eq_mid W₀ R b
    exact hne (by rw [eval_eq x hx, eval_eq y hy])
  let C' : Circuit := ⟨before ++ after.map (substConstGate k b), shiftDown k C.output⟩
  refine ⟨C', ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [C', List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g₀, hg₀, rfl⟩
    · exact hF g (List.mem_of_mem_take hg)
    · rcases hF g₀ (List.mem_of_mem_drop hg₀) with ⟨hop, hlen⟩
      exact substConstGate_fanInTwo k b g₀ hop hlen
  · intro g hg hop
    simp only [C', List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g₀, hg₀, rfl⟩
    · exact hN g (List.mem_of_mem_take hg) hop
    · exact substConstGate_notLeOne k b g₀ (hF g₀ (List.mem_of_mem_drop hg₀)).1 hop
  · simp only [Circuit.size, C', List.length_append, List.length_map, hblen, after, List.length_drop]
    omega
  · intro x hx
    unfold Circuit.eval
    rw [wires_eq_foldl, wires_eq_foldl]
    change ((before ++ after.map (substConstGate k b)).foldl gateStep x).getD (shiftDown k C.output) false =
      (C.gates.foldl gateStep x).getD C.output false
    rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_append]
    set W₀ := before.foldl gateStep x
    have hW₀len : W₀.length = k := by
      rw [foldl_gateStep_length, hx, hblen]
    have hstepj : [gj].foldl gateStep W₀ = W₀ ++ [b] := by
      simp only [List.foldl_cons, List.foldl_nil, gateStep, gj]
      rw [hb W₀ hW₀len]
    rw [hstepj]
    have hsim := foldl_sim_nil W₀ b after (substConstGate k b) (by
      intro g hg R
      have hgC : g ∈ C.gates := List.mem_of_mem_drop hg
      rw [← hW₀len]
      exact substConstGate_eval W₀ R b g (hF g hgC).1)
    rcases hsim with ⟨R, h1, h2⟩
    rw [h1, h2, ← hW₀len]
    exact getD_shiftDown W₀ R b C.output (by rwa [hW₀len])
  · intro w hw huse
    rcases huse with ⟨g, hg, hwg⟩ | hout
    · simp only [C', List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g₀, hg₀, rfl⟩
      · exact Or.inl ⟨g, List.mem_of_mem_take hg, hwg⟩
      · have hg₀C : g₀ ∈ C.gates := List.mem_of_mem_drop hg₀
        exact Or.inl ⟨g₀, hg₀C, substConstGate_mem_inputs (by omega) hw b g₀ (hF g₀ hg₀C).1 hwg⟩
    · simp only [C'] at hout
      unfold shiftDown at hout
      split_ifs at hout with hlt
      · exact Or.inr hout
      · omega

lemma deleteCopy (N : ℕ) (C : Circuit) (hF : FanInTwo C) (hN : NotLeOne C)
    (j : ℕ) (hj : j < C.gates.length) (a : ℕ) (ha_lt : a < N + j) (ha_mem : a ∈ (C.gates[j]).inputs)
    (ha : ∀ W₀ : List Bool, W₀.length = N + j →
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => W₀.getD i false) = W₀.getD a false) :
    ∃ C' : Circuit,
      FanInTwo C' ∧
      NotLeOne C' ∧
      C'.size + 1 = C.size ∧
      (∀ x : List Bool, x.length = N → C'.eval x = C.eval x) ∧
      (∀ w < N, UsesWire C' w → UsesWire C w) := by
  set k := N + j
  set before := C.gates.take j
  set gj := C.gates[j]
  set after := C.gates.drop (j + 1)
  have hsplit : C.gates = before ++ [gj] ++ after := list_split C.gates j hj
  have hblen : before.length = j := by simp [before, Nat.le_of_lt hj]
  let C' : Circuit := ⟨before ++ after.map (mapGate (remapCopy k a)), remapCopy k a C.output⟩
  refine ⟨C', ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [C', List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g₀, hg₀, rfl⟩
    · exact hF g (List.mem_of_mem_take hg)
    · rcases hF g₀ (List.mem_of_mem_drop hg₀) with ⟨hop, hlen⟩
      exact ⟨hop, by simpa [mapGate] using hlen⟩
  · intro g hg hop
    simp only [C', List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g₀, hg₀, rfl⟩
    · exact hN g (List.mem_of_mem_take hg) hop
    · simpa [mapGate] using hN g₀ (List.mem_of_mem_drop hg₀) hop
  · simp only [Circuit.size, C', List.length_append, List.length_map, hblen, after, List.length_drop]
    omega
  · intro x hx
    unfold Circuit.eval
    rw [wires_eq_foldl, wires_eq_foldl]
    change ((before ++ after.map (mapGate (remapCopy k a))).foldl gateStep x).getD (remapCopy k a C.output) false =
      (C.gates.foldl gateStep x).getD C.output false
    rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_append]
    set W₀ := before.foldl gateStep x
    have hW₀len : W₀.length = k := by
      rw [foldl_gateStep_length, hx, hblen]
    have hstepj : [gj].foldl gateStep W₀ = W₀ ++ [W₀.getD a false] := by
      simp only [List.foldl_cons, List.foldl_nil, gateStep, gj]
      rw [ha W₀ hW₀len]
    rw [hstepj]
    have hsim := foldl_sim_nil W₀ (W₀.getD a false) after (mapGate (remapCopy k a)) (by
      intro g _ R
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, ← hW₀len]
      exact getD_remapCopy W₀ R a (by omega) i)
    rcases hsim with ⟨R, h1, h2⟩
    rw [h1, h2, ← hW₀len]
    exact getD_remapCopy W₀ R a (by omega) C.output
  · intro w hw huse
    rcases huse with ⟨g, hg, hwg⟩ | hout
    · simp only [C', List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g₀, hg₀, rfl⟩
      · exact Or.inl ⟨g, List.mem_of_mem_take hg, hwg⟩
      · simp only [mapGate, List.mem_map] at hwg
        rcases hwg with ⟨i, hi, hrm⟩
        unfold remapCopy at hrm
        split_ifs at hrm with hlt heq
        · exact Or.inl ⟨g₀, List.mem_of_mem_drop hg₀, by rwa [← hrm]⟩
        · exact Or.inl ⟨gj, List.getElem_mem hj, by rwa [← hrm]⟩
        · omega
    · simp only [C'] at hout
      unfold remapCopy at hout
      split_ifs at hout with hlt heq
      · exact Or.inr hout
      · exact Or.inl ⟨gj, List.getElem_mem hj, by rwa [← hout]⟩
      · omega

lemma deleteDead (N : ℕ) (C : Circuit) (hF : FanInTwo C) (hN : NotLeOne C)
    (j : ℕ) (hj : j < C.gates.length)
    (hdead : ∀ g ∈ C.gates, N + j ∉ g.inputs)
    (hout_ne : C.output ≠ N + j) :
    ∃ C' : Circuit,
      FanInTwo C' ∧
      NotLeOne C' ∧
      C'.size + 1 = C.size ∧
      (∀ x : List Bool, x.length = N → C'.eval x = C.eval x) ∧
      (∀ w < N, UsesWire C' w → UsesWire C w) := by
  set k := N + j
  set before := C.gates.take j
  set gj := C.gates[j]
  set after := C.gates.drop (j + 1)
  have hsplit : C.gates = before ++ [gj] ++ after := list_split C.gates j hj
  have hblen : before.length = j := by simp [before, Nat.le_of_lt hj]
  let C' : Circuit := ⟨before ++ after.map (mapGate (shiftDown k)), shiftDown k C.output⟩
  refine ⟨C', ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [C', List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g₀, hg₀, rfl⟩
    · exact hF g (List.mem_of_mem_take hg)
    · rcases hF g₀ (List.mem_of_mem_drop hg₀) with ⟨hop, hlen⟩
      exact ⟨hop, by simpa [mapGate] using hlen⟩
  · intro g hg hop
    simp only [C', List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g₀, hg₀, rfl⟩
    · exact hN g (List.mem_of_mem_take hg) hop
    · simpa [mapGate] using hN g₀ (List.mem_of_mem_drop hg₀) hop
  · simp only [Circuit.size, C', List.length_append, List.length_map, hblen, after, List.length_drop]
    omega
  · intro x hx
    unfold Circuit.eval
    rw [wires_eq_foldl, wires_eq_foldl]
    change ((before ++ after.map (mapGate (shiftDown k))).foldl gateStep x).getD (shiftDown k C.output) false =
      (C.gates.foldl gateStep x).getD C.output false
    rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_append]
    set W₀ := before.foldl gateStep x
    have hW₀len : W₀.length = k := by
      rw [foldl_gateStep_length, hx, hblen]
    set v := gj.op.eval (gj.inputs.map fun i => W₀.getD i false)
    have hstepj : [gj].foldl gateStep W₀ = W₀ ++ [v] := by
      simp only [List.foldl_cons, List.foldl_nil, gateStep, v]
    rw [hstepj]
    have hsim := foldl_sim_nil W₀ v after (mapGate (shiftDown k)) (by
      intro g hg R
      have hgC : g ∈ C.gates := List.mem_of_mem_drop hg
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hik : i ≠ k := fun h => hdead g hgC (h ▸ hi)
      simp only [Function.comp_apply, ← hW₀len]
      exact getD_shiftDown W₀ R v i (by rwa [hW₀len]))
    rcases hsim with ⟨R, h1, h2⟩
    rw [h1, h2, ← hW₀len]
    exact getD_shiftDown W₀ R v C.output (by rwa [hW₀len])
  · intro w hw huse
    rcases huse with ⟨g, hg, hwg⟩ | hout
    · simp only [C', List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g₀, hg₀, rfl⟩
      · exact Or.inl ⟨g, List.mem_of_mem_take hg, hwg⟩
      · simp only [mapGate, List.mem_map] at hwg
        rcases hwg with ⟨i, hi, hsh⟩
        have hik : i ≠ k := fun h => hdead g₀ (List.mem_of_mem_drop hg₀) (h ▸ hi)
        unfold shiftDown at hsh
        split_ifs at hsh with hlt
        · exact Or.inl ⟨g₀, List.mem_of_mem_drop hg₀, by rwa [← hsh]⟩
        · omega
    · simp only [C'] at hout
      unfold shiftDown at hout
      split_ifs at hout with hlt
      · exact Or.inr hout
      · omega

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma readsIn_eq_zero_iff (C : Circuit) (w : ℕ) :
    readsIn C (Finset.range C.size) w = 0 ↔ ∀ g ∈ C.gates, w ∉ g.inputs := by
  unfold readsIn Circuit.size
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h g hg
    rcases List.mem_iff_getElem.mp hg with ⟨j, hj, rfl⟩
    have h0 := h j (Finset.mem_range.mpr hj)
    rw [gateAt_eq_getElem C j hj, List.count_eq_zero] at h0
    exact h0
  · intro h j hj
    have hj' : j < C.gates.length := Finset.mem_range.mp hj
    rw [gateAt_eq_getElem C j hj', List.count_eq_zero]
    exact h _ (List.getElem_mem hj')

lemma classify_bad_gate (k : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hnot : g.op = GateOp.not → g.inputs.length ≤ 1)
    (hbad : ¬ (((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
               (g.op = GateOp.not ∧ g.inputs.length = 1)) ∨
            ∃ i ∈ g.inputs, k ≤ i) :
    (∃ b : Bool, ∀ W₀ : List Bool, W₀.length = k →
      g.op.eval (g.inputs.map fun i => W₀.getD i false) = b) ∨
    (∃ a : ℕ, a < k ∧ a ∈ g.inputs ∧ ∀ W₀ : List Bool, W₀.length = k →
      g.op.eval (g.inputs.map fun i => W₀.getD i false) = W₀.getD a false) := by
  have hop' := (mem_op_iff g.op).mp hop
  rcases hop' with h1 | h2 | h3
  · rw [h1] at hbad ⊢
    cases hin : g.inputs with
    | nil =>
      left; exact ⟨true, fun _ _ => rfl⟩
    | cons a t =>
      cases t with
      | nil =>
        by_cases ha : a < k
        · right
          refine ⟨a, ha, by simp, fun W₀ _ => ?_⟩
          simp [GateOp.eval]
        · left
          refine ⟨false, fun W₀ hW => ?_⟩
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          exact getD_of_le_length W₀ a false (by omega)
      | cons b t2 =>
        cases t2 with
        | nil =>
          have hout : k ≤ a ∨ k ≤ b := by
            rcases hbad with hsh | ⟨i, hi, hik⟩
            · exfalso; apply hsh; left; simp [hin]
            · simp [hin] at hi
              rcases hi with rfl | rfl
              · exact Or.inl hik
              · exact Or.inr hik
          left
          refine ⟨false, fun W₀ hW => ?_⟩
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rcases hout with hka | hkb
          · rw [getD_of_le_length W₀ a false (by omega)]; rfl
          · rw [getD_of_le_length W₀ b false (by omega)]; simp
        | cons c t3 =>
          rw [hin] at hlen
          simp at hlen
  · rw [h2] at hbad ⊢
    cases hin : g.inputs with
    | nil =>
      left; exact ⟨false, fun _ _ => rfl⟩
    | cons a t =>
      cases t with
      | nil =>
        by_cases ha : a < k
        · right
          refine ⟨a, ha, by simp, fun W₀ _ => ?_⟩
          simp [GateOp.eval]
        · left
          refine ⟨false, fun W₀ hW => ?_⟩
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          exact getD_of_le_length W₀ a false (by omega)
      | cons b t2 =>
        cases t2 with
        | nil =>
          have hout : k ≤ a ∨ k ≤ b := by
            rcases hbad with hsh | ⟨i, hi, hik⟩
            · exfalso; apply hsh; left; simp [hin]
            · simp [hin] at hi
              rcases hi with rfl | rfl
              · exact Or.inl hik
              · exact Or.inr hik
          by_cases ha : a < k
          · have hkb : k ≤ b := by omega
            right
            refine ⟨a, ha, by simp, fun W₀ hW => ?_⟩
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            rw [getD_of_le_length W₀ b false (by omega)]
            simp
          · by_cases hb : b < k
            · have hka : k ≤ a := by omega
              right
              refine ⟨b, hb, by simp, fun W₀ hW => ?_⟩
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [getD_of_le_length W₀ a false (by omega)]
              rfl
            · left
              refine ⟨false, fun W₀ hW => ?_⟩
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [getD_of_le_length W₀ a false (by omega), getD_of_le_length W₀ b false (by omega)]
              rfl
        | cons c t3 =>
          rw [hin] at hlen
          simp at hlen
  · have hlen1 : g.inputs.length ≤ 1 := hnot h3
    rw [h3] at hbad ⊢
    cases hin : g.inputs with
    | nil =>
      left; exact ⟨true, fun _ _ => rfl⟩
    | cons a t =>
      cases t with
      | nil =>
        have hka : k ≤ a := by
          rcases hbad with hsh | ⟨i, hi, hik⟩
          · exfalso; apply hsh; right; simp [hin]
          · simp [hin] at hi
            rwa [← hi]
        left
        refine ⟨true, fun W₀ hW => ?_⟩
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
        rw [getD_of_le_length W₀ a false (by omega)]
        rfl
      | cons b t2 =>
        rw [hin] at hlen1
        simp at hlen1

lemma reduce_circuit (N : ℕ) : ∀ s : ℕ, ∀ C : Circuit,
    C.size ≤ s →
    FanInTwo C →
    NotLeOne C →
    (∃ x y : List Bool, x.length = N ∧ y.length = N ∧ C.eval x ≠ C.eval y) →
    ∃ D : Circuit,
      FanInTwo D ∧
      (∀ x : List Bool, x.length = N → D.eval x = C.eval x) ∧
      D.size ≤ C.size ∧
      (Reduced N D ∨ (D.size = 0 ∧ D.output < N)) ∧
      (∀ w < N, UsesWire D w → UsesWire C w) ∧
      (D.size + 1 ≤ C.size ∨ ∀ w < N, UsesWire C w → UsesWire D w) := by
  intro s
  induction s with
  | zero =>
    intro C hsize hF hN hNC
    have hsz0 : C.size = 0 := Nat.eq_zero_of_le_zero hsize
    have hout : C.output < N := by
      by_contra hge
      push Not at hge
      rcases hNC with ⟨x, y, hx, hy, hne⟩
      have hx0 : C.eval x = false := eval_of_ge_size C x (by omega)
      have hy0 : C.eval y = false := eval_of_ge_size C y (by omega)
      exact hne (by rw [hx0, hy0])
    exact ⟨C, hF, fun _ _ => rfl, le_refl _, Or.inr ⟨hsz0, hout⟩, fun _ _ h => h, Or.inr fun _ _ h => h⟩
  | succ s ih =>
    intro C hsize hF hN hNC
    by_cases hsz0 : C.size = 0
    · exact ih C (by omega) hF hN hNC
    · have hpos : 0 < C.size := Nat.pos_of_ne_zero hsz0
      by_cases hout_lt : C.output < N
      · let D : Circuit := ⟨[], C.output⟩
        refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg; simp [D] at hg
        · intro x hx
          unfold Circuit.eval
          have h1 : D.wires x = x := rfl
          rw [h1]
          exact (wires_getD_lt C x C.output (by omega)).symm
        · exact Nat.zero_le _
        · exact Or.inr ⟨rfl, hout_lt⟩
        · intro w _ huse
          rcases huse with ⟨g, hg, _⟩ | hout
          · simp [D] at hg
          · exact Or.inr hout
        · left
          change 0 + 1 ≤ C.size
          omega
      · have hout_lt_end : C.output < N + C.size := by
          by_contra hge
          push Not at hge
          rcases hNC with ⟨x, y, hx, hy, hne⟩
          have hx0 : C.eval x = false := eval_of_ge_size C x (by omega)
          have hy0 : C.eval y = false := eval_of_ge_size C y (by omega)
          exact hne (by rw [hx0, hy0])
        have step_down : ∀ C' : Circuit,
            FanInTwo C' →
            NotLeOne C' →
            C'.size + 1 = C.size →
            (∀ x : List Bool, x.length = N → C'.eval x = C.eval x) →
            (∀ w < N, UsesWire C' w → UsesWire C w) →
            ∃ D : Circuit,
              FanInTwo D ∧
              (∀ x : List Bool, x.length = N → D.eval x = C.eval x) ∧
              D.size ≤ C.size ∧
              (Reduced N D ∨ (D.size = 0 ∧ D.output < N)) ∧
              (∀ w < N, UsesWire D w → UsesWire C w) ∧
              (D.size + 1 ≤ C.size ∨ ∀ w < N, UsesWire C w → UsesWire D w) := by
          intro C' hF' hN' hsz' hev' huse'
          have hNC' : ∃ x y : List Bool, x.length = N ∧ y.length = N ∧ C'.eval x ≠ C'.eval y := by
            rcases hNC with ⟨x, y, hx, hy, hne⟩
            exact ⟨x, y, hx, hy, by rwa [hev' x hx, hev' y hy]⟩
          rcases ih C' (by omega) hF' hN' hNC' with ⟨D, hFD, hevD, hszD, hredD, huseD, _⟩
          exact ⟨D, hFD, fun x hx => by rw [hevD x hx, hev' x hx], by omega, hredD,
            fun w hw hu => huse' w hw (huseD w hw hu), Or.inl (by omega)⟩
        by_cases hgood : StrictShape C ∧ ReadsBack N C
        · rcases hgood with ⟨hsh, hrb⟩
          by_cases hdead : ∃ j < C.size, readsIn C (Finset.range C.size) (N + j) = 0 ∧ C.output ≠ N + j
          · rcases hdead with ⟨j, hj, hr0, hout_ne⟩
            have hdead' : ∀ g ∈ C.gates, N + j ∉ g.inputs := (readsIn_eq_zero_iff C (N + j)).mp hr0
            rcases deleteDead N C hF hN j hj hdead' hout_ne with ⟨C', hF', hN', hsz', hev', huse'⟩
            exact step_down C' hF' hN' hsz' hev' huse'
          · push Not at hdead
            have hlast_zero : readsIn C (Finset.range C.size) (N + (C.size - 1)) = 0 := by
              rw [readsIn_eq_zero_iff]
              intro g hg hmem
              rcases List.mem_iff_getElem.mp hg with ⟨t, ht, rfl⟩
              have hlt := hrb t ht (N + (C.size - 1)) (by rwa [gateAt_eq_getElem C t ht])
              change t < C.size at ht
              omega
            have hout_eq : C.output = N + (C.size - 1) :=
              hdead (C.size - 1) (by omega) hlast_zero
            have hout_plus : C.output + 1 = N + C.size := by omega
            have hreads_iff : ∀ j < C.size,
                readsIn C (Finset.range C.size) (N + j) = 0 ↔ j + 1 = C.size := by
              intro j hj
              constructor
              · intro hr0
                have heq : C.output = N + j := hdead j hj hr0
                omega
              · intro hjeq
                have hjlast : j = C.size - 1 := by omega
                rw [hjlast]
                exact hlast_zero
            exact ⟨C, hF, fun _ _ => rfl, le_refl _,
              Or.inl ⟨hsh, hrb, hpos, hout_plus, hreads_iff⟩,
              fun _ _ h => h, Or.inr fun _ _ h => h⟩
        · have hex : ∃ j : ℕ, ∃ hj : j < C.gates.length,
              (¬ (((C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) ∧ C.gates[j].inputs.length = 2) ∨
                  (C.gates[j].op = GateOp.not ∧ C.gates[j].inputs.length = 1))) ∨
              ∃ i ∈ C.gates[j].inputs, N + j ≤ i := by
            by_cases hsh : StrictShape C
            · have hnotrb : ¬ ReadsBack N C := fun hrb => hgood ⟨hsh, hrb⟩
              unfold ReadsBack at hnotrb
              push Not at hnotrb
              rcases hnotrb with ⟨j, hj, i, hi, hle⟩
              rw [gateAt_eq_getElem C j hj] at hi
              exact ⟨j, hj, Or.inr ⟨i, hi, hle⟩⟩
            · unfold StrictShape at hsh
              push Not at hsh
              rcases hsh with ⟨g, hg, hng⟩
              rcases List.mem_iff_getElem.mp hg with ⟨j, hj, rfl⟩
              exact ⟨j, hj, Or.inl (by
                intro h
                rcases h with ⟨hor, hlen⟩ | ⟨hnot, hlen⟩
                · exact hng.1 hor hlen
                · exact hng.2 hnot hlen)⟩
          rcases hex with ⟨j, hj, hbad⟩
          have hgF := hF (C.gates[j]) (List.getElem_mem hj)
          have hgN := hN (C.gates[j]) (List.getElem_mem hj)
          rcases classify_bad_gate (N + j) (C.gates[j]) hgF.1 hgF.2 hgN hbad with
            ⟨b, hb⟩ | ⟨a, ha_lt, ha_mem, ha⟩
          · rcases deleteConst N C hF hN hNC j hj b hb with ⟨C', hF', hN', hsz', hev', huse'⟩
            exact step_down C' hF' hN' hsz' hev' huse'
          · rcases deleteCopy N C hF hN j hj a ha_lt ha_mem ha with ⟨C', hF', hN', hsz', hev', huse'⟩
            exact step_down C' hF' hN' hsz' hev' huse'

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

lemma main :
    ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.Represents.Represents A C →
      (∃ (u u2 : Fin n) (v v2 : Fin m), A u v ≠ A u2 v2) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D ∧
        PEqualNP.Represents.Represents A D ∧
        D.size ≤ C.size ∧
        (((∀ g ∈ D.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) D ∧
          0 < D.size ∧
          D.output + 1 = (n + m) + D.size ∧
          (∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) ((n + m) + j) = 0 ↔ j + 1 = D.size))) ∨
         (D.size = 0 ∧ D.output < (n + m))) ∧
        (∀ w < (n + m), ((∃ g ∈ D.gates, w ∈ g.inputs) ∨ D.output = w) → ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ w ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some w)) ∨ C.output = w)) ∧
        (D.size + 1 ≤ C.size ∨ ∀ w < (n + m), ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ w ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some w)) ∨ C.output = w) → ((∃ g ∈ D.gates, w ∈ g.inputs) ∨ D.output = w)) := by
  intro n m A C hF hRep hNC
  let C₀ := stripNot C
  have hF0 : FanInTwo C₀ := stripNot_fanInTwo C hF
  have hN0 : NotLeOne C₀ := stripNot_notLeOne C
  have hsz0 : C₀.size = C.size := stripNot_size C
  have hNC0 : ∃ x y : List Bool, x.length = n + m ∧ y.length = n + m ∧ C₀.eval x ≠ C₀.eval y := by
    rcases hNC with ⟨u, u2, v, v2, hne⟩
    refine ⟨oneEach u v, oneEach u2 v2, oneEach_length u v, oneEach_length u2 v2, ?_⟩
    rw [stripNot_eval, stripNot_eval, hRep u v, hRep u2 v2]
    exact hne
  rcases reduce_circuit (n + m) C₀.size C₀ (le_refl _) hF0 hN0 hNC0 with
    ⟨D, hFD, hevD, hszD, hredD, huse1, huse2⟩
  refine ⟨D, hFD, ?_, ?_, hredD, ?_, ?_⟩
  · intro u v
    rw [hevD (oneEach u v) (oneEach_length u v), stripNot_eval, hRep u v]
  · omega
  · intro w hw hDw
    exact (stripNot_usesWire_iff C hF w).mp (huse1 w hw hDw)
  · rcases huse2 with hlt | hkeep
    · exact Or.inl (by omega)
    · right
      intro w hw hCw
      exact hkeep w hw ((stripNot_usesWire_iff C hF w).mpr hCw)

end PEqualNP.Outside.L_meta_24613

theorem PEqualNP.Outside.L_meta_24613 : (∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (∃ (u u2 : Fin n) (v v2 : Fin m), A u v ≠ A u2 v2) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.Represents.Represents A D ∧ D.size ≤ C.size ∧ (((∀ g ∈ D.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) D ∧ 0 < D.size ∧ D.output + 1 = (n + m) + D.size ∧ (∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) ((n + m) + j) = 0 ↔ j + 1 = D.size))) ∨ (D.size = 0 ∧ D.output < (n + m))) ∧ (∀ w < (n + m), ((∃ g ∈ D.gates, w ∈ g.inputs) ∨ D.output = w) → ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ w ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some w)) ∨ C.output = w)) ∧ (D.size + 1 ≤ C.size ∨ ∀ w < (n + m), ((∃ g ∈ C.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ w ∈ g.inputs) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some w)) ∨ C.output = w) → ((∃ g ∈ D.gates, w ∈ g.inputs) ∨ D.output = w))) := by
  exact PEqualNP.Outside.L_meta_24613.main
