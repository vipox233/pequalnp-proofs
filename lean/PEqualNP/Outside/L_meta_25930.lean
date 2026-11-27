import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25930

namespace Norm

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

end Norm

namespace Rows
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.EdgeOwnership PEqualNP.Core PEqualNP.MetaComplexity.NestedCover

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem snoc {α : Type} (l : List α) (b d : α) (w : ℕ) :
    (l ++ [b]).getD w d = if w < l.length then l.getD w d else if w = l.length then b else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem agree (N : ℕ) (B D : ℕ → Prop) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ w, ¬ B w → x.getD w false = y.getD w false) (gs : List Gate) :
    (∀ j, D j → ∀ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, ¬ B w ∧ (N ≤ w → w < N + j → D (w - N))) →
    ∀ w, ¬ B w → (N ≤ w → w < N + gs.length → D (w - N)) →
      (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn with
  | nil => exact fun _ w hb _ => hxy w hb
  | append_singleton gs g ih =>
    intro hD w hb hw
    have ih := ih (fun j hj i hi => by
      by_cases hj' : j < gs.length
      · refine hD j hj i ?_
        rwa [snoc, if_pos hj']
      · rw [List.getD_eq_default _ _ (by omega)] at hi; simp at hi)
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [snoc, snoc, len, len, hx, hy]
    split_ifs with h1 h2
    · exact ih w hb fun a _ => hw a (by simp; omega)
    · have hj : D gs.length := by
        have := hw (by omega) (by simp; omega); rwa [h2, Nat.add_sub_cancel_left] at this
      congr 1
      refine List.map_congr_left fun i hi => ?_
      obtain ⟨hb', hc⟩ := hD _ hj i (by simpa [snoc] using hi)
      exact ih i hb' hc
    · rfl

theorem clen (n : ℕ) (gs : List Gate) : (gs.foldl (coneStep n) []).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => simp [List.foldl_append, coneStep, ih]

theorem cmem (n : ℕ) (gs : List Gate) : ∀ j i, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
    (j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
      (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro j i; simp
  | append_singleton gs g ih =>
    intro j i
    have hl := clen n gs
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize gs.foldl (coneStep n) [] = F at ih hl ⊢
    unfold coneStep
    have e : ∀ k b, k < gs.length → (F ++ [b]).getD k [] = F.getD k [] := fun k b hk => by
      rw [snoc, if_pos (by omega)]
    rw [snoc, snoc, hl]
    split_ifs with h1 h2
    · rw [ih j i]
      constructor
      · rintro ⟨-, w, hw, h3, h4, h5⟩
        exact ⟨by simp; omega, w, hw, h3, h4, by rwa [e _ _ (by omega)]⟩
      · rintro ⟨-, w, hw, h3, h4, h5⟩
        exact ⟨h1, w, hw, h3, h4, by rwa [e _ _ (by omega)] at h5⟩
    · subst h2
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h3, h4⟩, h5⟩
        exact ⟨by simp, w, hw, h3, h4, by rwa [e _ _ (by omega)]⟩
      · rintro ⟨-, w, hw, h3, h4, h5⟩
        exact ⟨w, ⟨hw, h3, h4⟩, by rwa [e _ _ (by omega)] at h5⟩
    · simp

theorem ctrans (n : ℕ) (C : Circuit) : ∀ j i k, InCone n C i j → InCone n C k i → InCone n C k j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ihj =>
    intro i k hi hk
    unfold InCone cones at *
    obtain ⟨hj, w, hw, h3, h4, h5⟩ := (cmem n C.gates j i).1 hi
    refine (cmem n C.gates j k).2 ⟨hj, w, hw, h3, h4, Or.inr ?_⟩
    rcases h5 with rfl | h5
    · exact hk
    · exact ihj _ (by omega) i k h5 hk

theorem oclosed (N : ℕ) (C : Circuit) (j : ℕ) (hj : InOutputCone N C j) (w : ℕ)
    (hw : w ∈ (gateAt C j).inputs) (h1 : N ≤ w) (h2 : w < N + j) : InOutputCone N C (w - N) := by
  have hd : InCone N C (w - N) j := by
    unfold InCone cones
    exact (cmem N C.gates j _).2 ⟨hj.1, w, hw, h1, h2, Or.inl rfl⟩
  refine ⟨by have := hj.1; omega, Or.inr ?_⟩
  rcases hj.2 with h | ⟨h3, h4⟩
  · exact ⟨by omega, by rwa [h, Nat.add_sub_cancel_left]⟩
  · exact ⟨h3, ctrans N C _ _ _ h4 hd⟩

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem silent (N : ℕ) (C : Circuit) (B : ℕ → Prop)
    (hB : ∀ j, InOutputCone N C j → ∀ w ∈ (gateAt C j).inputs, ¬ B w) (ho : ¬ B C.output)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ w, ¬ B w → x.getD w false = y.getD w false) : C.eval x = C.eval y :=
  agree N B (InOutputCone N C) x y hx hy hxy C.gates
    (fun j hj w hw => ⟨hB j hj w hw, oclosed N C j hj w hw⟩) _ ho
    (fun h1 h2 => ⟨by omega, Or.inl (by omega)⟩)

theorem gd (C : Circuit) {j : ℕ} (h : j < C.gates.length) :
    C.gates.getD j ⟨GateOp.and, []⟩ = gateAt C j := by
  rw [gateAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

end Rows

open Rows PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.EdgeOwnership PEqualNP.Core PEqualNP.MetaComplexity.NestedCover  in
theorem rowSilent : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (u u' : Fin n), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (C.output ≠ u.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → u.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → (C.output ≠ u'.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → u'.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∀ v : Fin m, A u v = A u' v := by
  intro n m A C u u' _ hR hu hu' v
  rw [← hR u v, ← hR u' v]
  refine silent (n + m) C (fun w => w = u.val ∨ w = u'.val)
    (fun j hj w hw h => h.elim (fun e => hu.2 j hj.1 hj.2 (by rw [gd C hj.1]; exact e ▸ hw)) (fun e => hu'.2 j hj.1 hj.2 (by rw [gd C hj.1]; exact e ▸ hw)))
    (fun h => h.elim hu.1 hu'.1) _ _ (by simp [oneEach]) (by simp [oneEach]) fun w hw => ?_
  refine Bool.eq_iff_iff.2 ?_
  rw [oe, oe]; constructor <;> intro h <;> omega

namespace Cols

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

private def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_wstep_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl wstep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [wstep]
    omega

private lemma oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

private lemma oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : Fin n) :
    (oneEach u v).getD i.val false = decide (i = u) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

private lemma oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) (j : Fin m) :
    (oneEach u v).getD (n + j.val) false = decide (j = v) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, j.isLt]

private lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

private lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
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
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

private lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
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

private lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

private lemma outsideLength (xs : List Bool) (i : ℕ) (h : xs.length ≤ i) :
    xs.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private lemma snocOther (xs : List Bool) (b : Bool) (i : ℕ) (h : i ≠ xs.length) :
    (xs ++ [b]).getD i false = xs.getD i false := by
  by_cases hi : i < xs.length
  · exact List.getD_append _ _ _ _ hi
  · rw [outsideLength _ _ (by simp; omega), outsideLength _ _ (by omega)]

lemma full (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit) (v v' : Fin m)
    (rep : Represents A C)
    (silent : ∀ z ∈ [v,v'], C.output ≠ n+z.val ∧ ∀ j < C.gates.length,
      (C.output = n+m+j ∨ (n+m ≤ C.output ∧ InCone (n+m) C j (C.output-(n+m)))) →
        n+z.val ∉ (C.gates.getD j ⟨GateOp.and, []⟩).inputs) (u : Fin n) :
    A u v = A u v' := by
  let N := n+m
  let W := fun (k : ℕ) (z : Fin m) => (C.gates.take k).foldl wstep (oneEach u z)
  let live := fun j => C.output = N+j ∨ (N ≤ C.output ∧ InCone N C j (C.output-N))
  let needed := fun w => (w < N ∧ w ≠ n+v.val ∧ w ≠ n+v'.val) ∨ (N ≤ w ∧ live (w-N))
  have wlen (k : ℕ) (z : Fin m) (h : k ≤ C.gates.length) : (W k z).length = N+k := by
    simp [W,foldl_wstep_len,oneEach_len,N,Nat.min_eq_left h]
  have eqs (k : ℕ) (hk : k ≤ C.gates.length) (w : ℕ) (hw : needed w) :
      (W k v).getD w false = (W k v').getD w false := by
    induction k generalizing w with
    | zero =>
      change (oneEach u v).getD w false = (oneEach u v').getD w false
      rcases hw with ⟨hb, hv, hv'⟩ | ⟨hb,_⟩
      · by_cases hl : w < n
        · exact (oneEach_getD_left u v ⟨w,hl⟩).trans (oneEach_getD_left u v' ⟨w,hl⟩).symm
        · let z : Fin m := ⟨w-n, by dsimp [N] at hb; omega⟩
          have hz : n+z.val=w := by dsimp [z]; omega
          have h1 : z ≠ v := fun h => hv (hz ▸ congrArg (fun x : Fin m => n+x.val) h)
          have h2 : z ≠ v' := fun h => hv' (hz ▸ congrArg (fun x : Fin m => n+x.val) h)
          rw [←hz, oneEach_getD_right, oneEach_getD_right]
          simp [h1,h2]
      · rw [outsideLength _ _ (by rw [oneEach_len]; exact hb),
            outsideLength _ _ (by rw [oneEach_len]; exact hb)]
    | succ k ih =>
      have hk' : k < C.gates.length := by omega
      let g := C.gates[k]
      have hg1 : C.gates.getD k ⟨GateOp.and,[]⟩ = g := by simp [g,List.getD_eq_getElem?_getD,hk']
      have hg2 : gateAt C k = g := by simp [gateAt,g,List.getD_eq_getElem?_getD,hk']
      have step (z : Fin m) : W (k+1) z = W k z ++ [g.op.eval (g.inputs.map fun i => (W k z).getD i false)] := by
        simp only [W,List.take_succ_eq_append_getElem hk',List.foldl_append,List.foldl_cons,List.foldl_nil,wstep,g]
      rw [step,step]
      by_cases he : w=N+k
      · subst w
        have hl : live k := by
          rcases hw with ⟨h,_,_⟩ | ⟨_,h⟩
          · omega
          · simpa using h
        have inputEq : ∀ i ∈ g.inputs, (W k v).getD i false = (W k v').getD i false := by
          intro i hi
          by_cases hp : i < N
          · apply ih (by omega) i (Or.inl ⟨hp,?_,?_⟩)
            · intro e
              exact (silent v (by simp)).2 k hk' hl (hg1 ▸ e ▸ hi)
            · intro e
              exact (silent v' (by simp)).2 k hk' hl (hg1 ▸ e ▸ hi)
          · by_cases hearly : i < N+k
            · have edge : InCone N C (i-N) k := by
                apply (inCone_iff _ _ _ _).2
                refine ⟨hk',i-N,by omega,?_,Or.inl rfl⟩
                rwa [hg2,show N+(i-N)=i by omega]
              apply ih (by omega) i (Or.inr ⟨by omega, Or.inr ?_⟩)
              rcases hl with hout | ⟨hout,con⟩
              · exact ⟨by omega, by simpa [hout] using edge⟩
              · exact ⟨hout,inCone_trans _ _ _ _ edge _ con⟩
            · rw [outsideLength _ _ (by rw [wlen k v (by omega)]; omega),
                  outsideLength _ _ (by rw [wlen k v' (by omega)]; omega)]
        have maps := List.map_congr_left inputEq
        rw [maps, List.getD_append_right _ _ _ _ (by rw [wlen k v (by omega)]),
            List.getD_append_right _ _ _ _ (by rw [wlen k v' (by omega)])]
        rw [wlen k v (by omega),wlen k v' (by omega)]
      · rw [snocOther _ _ _ (by rwa [wlen k v (by omega)]),snocOther _ _ _ (by rwa [wlen k v' (by omega)])]
        exact ih (by omega) w hw
  have hn : needed C.output := by
    by_cases h : C.output < N
    · exact Or.inl ⟨h,(silent v (by simp)).1,(silent v' (by simp)).1⟩
    · exact Or.inr ⟨by omega,Or.inl (by omega)⟩
  rw [← rep u v, ← rep u v']
  change (C.gates.foldl wstep (oneEach u v)).getD C.output false =
    (C.gates.foldl wstep (oneEach u v')).getD C.output false
  simpa only [W,List.take_length] using eqs C.gates.length le_rfl C.output hn

end Cols

theorem colSilent : (∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (v v' : Fin m), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (C.output ≠ (n + v.val) ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → (n + v.val) ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → (C.output ≠ (n + v'.val) ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → (n + v'.val) ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∀ u : Fin n, A u v = A u v') := by
  intro n m A C v v' _ rep sv sv' u
  apply Cols.full n m A C v v' rep _ u
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl
  · exact sv
  · exact sv'

namespace Slots
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem sum_count (l : List ℕ) (N : ℕ) (h : ∀ i ∈ l, i < N) :
    ∑ w ∈ Finset.range N, l.count w = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a < N := h a (by simp)
    rw [List.length_cons, ← ih (fun i hi => h i (by simp [hi]))]
    simp [List.count_cons, Finset.sum_add_distrib, ha]

theorem key (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) :
    (∑ w ∈ Finset.range m, readsIn C (Finset.range C.size) w) +
      (∑ j ∈ Finset.range C.size, readsIn C (Finset.range C.size) (m + j)) =
    ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.length := by
  rw [← Finset.sum_range_add]
  unfold readsIn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => sum_count _ _ fun i hi => ?_
  have h1 : j < C.size := Finset.mem_range.mp hj
  have := hrb j h1 i hi
  omega

theorem slots (C : Circuit)
    (hg : ∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    (∑ j ∈ Finset.range C.size, (gateAt C j).inputs.length) +
      (@Finset.filter ℕ (fun k => (gateAt C k).op = GateOp.not) (fun d1 => Classical.propDecidable _)
        (Finset.range C.size)).card = C.size + C.size := by
  rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.sum_congr rfl (g := fun _ => 2) ?_]
  · simp [Circuit.size]
    omega
  · intro j hj
    have hj' : j < C.gates.length := Finset.mem_range.mp hj
    have hmem : gateAt C j ∈ C.gates := by
      simp only [gateAt, List.getD_eq_getElem _ _ hj']
      exact List.getElem_mem hj'
    rcases hg _ hmem with ⟨h1 | h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem tail (s : ℕ) (f : ℕ → ℕ) (hs : 0 < s) (h : ∀ j < s, (f j = 0 ↔ j + 1 = s)) :
    (∑ j ∈ Finset.range (s - 1), (f j - 1)) + (s - 1) = ∑ j ∈ Finset.range s, f j := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hk : f k = 0 := (h k (by omega)).2 rfl
  simp only [Nat.add_sub_cancel, Finset.sum_range_succ, hk, Nat.add_zero]
  have : ∀ j ∈ Finset.range k, f j - 1 + 1 = f j := fun j hj => by
    have hj' : j < k := Finset.mem_range.mp hj
    have : f j ≠ 0 := fun h0 => by have := (h j (by omega)).1 h0; omega
    omega
  rw [← Finset.sum_congr rfl this, Finset.sum_add_distrib]
  simp

end Slots

open Slots in
theorem account : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
  (C.size + C.size =
      (∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ Finset.range C.size,
        PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j)) +
      (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d1 => Classical.propDecidable _)
          (Finset.range C.size)).card) ∧
  (C.size + 1 =
      (∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
          (Finset.range C.size),
        (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1)) +
      (@Finset.filter ℕ (fun k2 => (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d3 => Classical.propDecidable _)
          (Finset.range C.size)).card) := by
  intro m C hg hrb hpos hlast
  have hk := key m C hrb
  have hs := slots C hg
  have hf : @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d2 => Classical.propDecidable _)
      (Finset.range C.size) = Finset.range (C.size - 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have ht := tail C.size (fun j => PEqualNP.MetaComplexity.NestedCover.readsIn C
    (Finset.range C.size) (m + j)) hpos hlast
  rw [hf]
  constructor <;> omega

lemma profileCost {n a : Nat} (f : Fin n → Nat) (R : Fin n → Fin n → Prop) [DecidableRel R]
    (cap : ∀ i, (Finset.univ.filter (fun j => R j i)).card ≤ a)
    (same : ∀ i j, f i = 0 → f j = 0 → R i j) : n ≤ (∑ i, f i) + a := by
  classical
  let Z := Finset.univ.filter (fun i => f i = 0)
  have zcap : Z.card ≤ a := by
    by_cases hz : Z.Nonempty
    · obtain ⟨i, hi⟩ := hz
      apply le_trans _ (cap i)
      apply Finset.card_le_card
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, same j i (Finset.mem_filter.mp hj).2
        (Finset.mem_filter.mp hi).2⟩
    · simp [Finset.not_nonempty_iff_eq_empty.mp hz]
  have cover : (∑ _ : Fin n, 1 : Nat) ≤ ∑ i : Fin n, ((if f i = 0 then 1 else 0) + f i) := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> omega
  rw [Finset.sum_add_distrib, ← Finset.card_filter] at cover
  change (∑ _ : Fin n, 1 : Nat) ≤ Z.card + ∑ i, f i at cover
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at cover
  omega

end PEqualNP.Outside.L_meta_25930

open PEqualNP.Outside.L_meta_25930 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.L_meta_25930 : (∀ (n m a b s : ℕ) (G : Fin n → Fin m → Bool),
  (∃ (r t : Fin n) (c u : Fin m), G r c ≠ G t u) →
  (∀ r : Fin n, (Finset.univ.filter (fun t : Fin n => ∀ c : Fin m, G t c = G r c)).card ≤ a) →
  (∀ c : Fin m, (Finset.univ.filter (fun u : Fin m => ∀ r : Fin n, G r u = G r c)).card ≤ b) →
  s + a + b < n + m →
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ s ∧ PEqualNP.Represents.Represents G C) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
    D.size ≤ s ∧ PEqualNP.Represents.Represents G D) := by
  classical
  rintro n m a b s G nonconst rowCap colCap low ⟨C, hC, hcsize, repC⟩
  obtain ⟨D, fan, rep, dsize, form, _, _⟩ := Norm.main n m G C hC repC nonconst
  refine ⟨D, ?_, dsize.trans hcsize, rep⟩
  rcases form with ⟨shape, back, pos, output, live⟩ | ⟨h0, _⟩
  · let count (w : Nat) := readsIn D (Finset.range D.size) w
    have silent (w : Nat) (hw : count w = 0) (j : Nat) (hj : j < D.gates.length) :
        w ∉ (D.gates.getD j ⟨GateOp.and, []⟩).inputs := by
      rw [List.getD_eq_getElem _ _ hj]
      exact (Norm.readsIn_eq_zero_iff D w).mp hw _ (List.getElem_mem hj)
    have row : n ≤ (∑ i : Fin n, count i.val) + a := by
      apply profileCost (fun i : Fin n => count i.val) (fun i j => ∀ c, G i c = G j c) rowCap
      intro i j hi hj
      apply rowSilent n m G D i j fan rep
      · exact ⟨by have := i.isLt; omega, fun u hu _ => silent i.val hi u hu⟩
      · exact ⟨by have := j.isLt; omega, fun u hu _ => silent j.val hj u hu⟩
    have col : m ≤ (∑ i : Fin m, count (n+i.val)) + b := by
      apply profileCost (fun i : Fin m => count (n+i.val)) (fun i j => ∀ r, G r i = G r j) colCap
      intro i j hi hj
      apply colSilent n m G D i j fan rep
      · exact ⟨by have := i.isLt; omega, fun u hu _ => silent (n+i.val) hi u hu⟩
      · exact ⟨by have := j.isLt; omega, fun u hu _ => silent (n+j.val) hj u hu⟩
    rw [Fin.sum_univ_eq_sum_range count] at row
    rw [Fin.sum_univ_eq_sum_range (fun j => count (n+j))] at col
    have total : n + m ≤ (∑ w ∈ Finset.range (n+m), count w) + a + b := by
      rw [Finset.sum_range_add]
      omega
    let N := (Finset.range D.size).filter (fun j => (gateAt D j).op = GateOp.not)
    have slots := (account (n+m) D shape back pos live).2
    change D.size + 1 = (∑ w ∈ Finset.range (n+m), count w) + _ + N.card at slots
    have empty : N = ∅ := Finset.card_eq_zero.mp (by omega)
    intro g hg
    rcases shape g hg with ⟨op, arity⟩ | ⟨neg, _⟩
    · exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using op, arity.le⟩
    · obtain ⟨j, hj, eq⟩ := List.mem_iff_getElem.mp hg
      have mem : j ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,
        by rw [Norm.gateAt_eq_getElem D j hj, eq]; exact neg⟩
      simp [empty] at mem
  · have nil : D.gates = [] := List.length_eq_zero_iff.mp h0
    intro g hg
    simp [nil] at hg
