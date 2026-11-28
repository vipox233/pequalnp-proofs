import PEqualNP.Defs

-- The restriction compiler and wire evaluation lemmas are adapted from
-- Ryan Thompson, L-meta-19118, PR 24713 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_33687_aux

open PEqualNP.CircuitLowerBounds

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

def Const {Y : Type} (f : Y → Bool) : Prop := ∃ c, ∀ y, f y = c

def Drop {Y : Type} (n : ℕ) (F : ℕ → Y → Bool) (j : ℕ) : Prop :=
  Const (F (n + j)) ∨ ∃ w < n + j, ∀ y, F (n + j) y = F w y

local instance : DecidableEq GateOp := lineDegreeGateOpDecEq

def countNot (gs : List Gate) : Nat :=
  (gs.filter fun (g : Gate) => decide (g.op = GateOp.not)).length

theorem countNot_append (gs hs : List Gate) :
    countNot (gs ++ hs) = countNot gs + countNot hs := by
  simp [countNot, List.filter_append]

theorem restrict (n m : ℕ) (gs : List Gate) (F : ℕ → (Fin m → Bool) → Bool)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hin : ∀ i < n, Const (F i) ∨ ∃ k < m, ∀ y, F i y = (List.ofFn y).getD k false)
    (hF : ∀ (j : ℕ) (hj : j < gs.length) (y : Fin m → Bool), F (n + j) y =
      gs[j].op.eval (gs[j].inputs.map fun i => if i < n + j then F i y else false)) :
    ∀ K ≤ gs.length, ∃ (ds : List Gate) (S : Finset ℕ),
      (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
      (∀ j ∈ S, j < K ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
      countNot ds ≤ countNot (gs.take K) ∧
      ∀ w < n + K, Const (F w) ∨
        ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨[], ∅, by simp, by simp, by simp, by simp, by simp [countNot], fun w hw => ?_⟩
    simpa [run] using hin w (by omega)
  | succ K ih =>
    intro hK
    obtain ⟨ds, S, h1, hb, h2, h3, hn, h4⟩ := ih (by omega)
    have hj : K < gs.length := by omega
    have ht := List.take_succ_eq_append_getElem hj
    have hn' : countNot ds ≤ countNot (gs.take (K + 1)) := by
      rw [ht, countNot_append]
      omega
    have h2' : ∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j := fun j hj =>
      ⟨by have := (h2 j hj).1; omega, (h2 j hj).2⟩
    by_cases hd : Drop n F K
    · refine ⟨ds, S, h1, hb, h2', h3, hn', fun w hw => ?_⟩
      rcases Nat.lt_or_ge w (n + K) with h | h
      · exact h4 w h
      · rw [show w = n + K by omega]
        rcases hd with hc | ⟨u, hu, he⟩
        · exact Or.inl hc
        · rcases h4 u hu with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
          · exact Or.inl ⟨c, fun y => (he y).trans (hc y)⟩
          · exact Or.inr ⟨k, hk, fun y => (he y).trans (hk' y)⟩
    · have hnc : ¬ Const (F (n + K)) := fun h => hd (Or.inl h)
      have hne : ∀ u < n + K, ¬ ∀ y, F (n + K) y = F u y := fun u hu h => hd (Or.inr ⟨u, hu, h⟩)
      have addg : ∀ g : Gate, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
          g.op = gs[K].op → g.inputs.length ≤ 2 → (∀ i ∈ g.inputs, i < m + ds.length) →
          (∀ y, F (n + K) y = g.op.eval (g.inputs.map fun i =>
            (run ds (List.ofFn y)).getD i false)) →
          ∃ (ds : List Gate) (S : Finset ℕ),
            (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
              g.inputs.length ≤ 2) ∧
            (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
            (∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
            countNot ds ≤ countNot (gs.take (K + 1)) ∧
            ∀ w < n + (K + 1), Const (F w) ∨
              ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
        intro g ho heq hl hgb hg
        have hKS : K ∉ S := fun h => by have := (h2 K h).1; omega
        refine ⟨ds ++ [g], insert K S, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.1 hg' with h | h
          · exact h1 g' h
          · rw [List.mem_singleton.1 h]; exact ⟨ho, hl⟩
        · intro j hj i hi
          rcases Nat.lt_or_ge j ds.length with h | h
          · rw [List.getElem_append_left h] at hi
            exact hb j h i hi
          · have hjj : j = ds.length := by simp at hj; omega
            subst hjj
            exact hgb i (by simpa using hi)
        · intro j hj
          rcases Finset.mem_insert.1 hj with rfl | h
          · exact ⟨by omega, hd⟩
          · exact h2' j h
        · rw [Finset.card_insert_of_notMem hKS]; simp; omega
        · rw [ht, countNot_append, countNot_append]
          have hsingle : countNot [g] = countNot [gs[K]] := by
            simp only [countNot, List.filter_cons, List.filter_nil, heq]
            split <;> rfl
          omega
        · intro w hw
          rcases Nat.lt_or_ge w (n + K) with h | h
          · rcases h4 w h with hc | ⟨k, hk, hk'⟩
            · exact Or.inl hc
            · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
              rw [run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_ofFn]; exact hk)]
              exact hk' y
          · refine Or.inr ⟨m + ds.length, by simp, fun y => ?_⟩
            have hl' : (run ds (List.ofFn y)).length = m + ds.length := by
              rw [run_length, List.length_ofFn]
            rw [show w = n + K by omega, run_snoc, ← hl', getD_at]
            exact hg y
      have hval : ∀ i, (∃ c, ∀ y, (if i < n + K then F i y else false) = c) ∨
          (i < n + K ∧ ∃ k < m + ds.length, ∀ y,
            F i y = (run ds (List.ofFn y)).getD k false) := by
        intro i
        by_cases hi : i < n + K
        · rcases h4 i hi with ⟨c, hc⟩ | h
          · exact Or.inl ⟨c, fun y => by rw [if_pos hi]; exact hc y⟩
          · exact Or.inr ⟨hi, h⟩
        · exact Or.inl ⟨false, fun y => by rw [if_neg hi]⟩
      have hFK := hF K hj
      obtain ⟨hop, hlen⟩ := hops _ (List.getElem_mem hj)
      generalize gs[K].inputs = I at *
      generalize gs[K].op = o at *
      match I, hlen with
      | [], _ =>
        refine absurd ⟨o.eval [], fun y => ?_⟩ hnc
        simpa using hFK y
      | [a], _ =>
        rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
        · refine absurd ⟨o.eval [c], fun y => ?_⟩ hnc
          rw [hFK y, List.map_singleton, hc y]
        · rcases hop with rfl | rfl | rfl
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) rfl (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]
      | [a, b], _ =>
        rcases hop with rfl | rfl | rfl
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c && if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · exact absurd ⟨false, fun y => by rw [he y]; rfl⟩ hnc
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y && c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd ⟨false, fun y => by rw [he y]; simp⟩ hnc
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
            · refine addg ⟨GateOp.and, [k, l]⟩ (by simp) rfl (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c || if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
            · exact absurd ⟨true, fun y => by rw [he y]; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y || c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
              · exact absurd ⟨true, fun y => by rw [he y]; simp⟩ hnc
            · refine addg ⟨GateOp.or, [k, l]⟩ (by simp) rfl (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · refine absurd ⟨!c, fun y => ?_⟩ hnc
            rw [hFK y, List.map_cons, hc y]; simp [GateOp.eval]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) rfl (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)


def rds (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (u v : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huv : ∀ i ∈ rds g, u i = v i) : g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  rcases hop with h | h | h
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [h]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      have := huv a (by simp [hi])
      simp [GateOp.eval, this]

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem indep (v : ℕ) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hno : ∀ g ∈ gs, v ∉ rds g) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
    ∀ i, i ≠ v → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hxy
  | append_singleton gs g ih =>
    have ih' := ih (fun g' h => hop g' (by simp [h])) (fun g' h => hno g' (by simp [h]))
    intro i hi
    have e : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs y).getD i false) :=
      eval_congr g _ _ (hop g (by simp)) fun k hk =>
        ih' k fun hc => hno g (by simp) (hc ▸ hk)
    rw [run_snoc, run_snoc, getD_sn, getD_sn, run_length, run_length, hl, e]
    split_ifs
    · rfl
    · exact ih' i hi

theorem one_drop (n q : ℕ) (C : Circuit) (tap : Fin q → Nat)
    (hC : PEqualNP.MetaComplexity.FanInTwo C) (i : Fin n) (b : Bool)
    (hess : ∃ (j : Fin q) (x y : Fin n → Bool), (∀ k, k ≠ i → x k = y k) ∧
      (C.wires (List.ofFn x)).getD (tap j) false ≠
        (C.wires (List.ofFn y)).getD (tap j) false)
    (hnc : ∀ j, ¬ Const (fun y : Fin n → Bool =>
      (C.wires (List.ofFn (Function.update y i b))).getD (tap j) false)) :
    ∃ (D : Circuit) (out : Fin q → Nat), PEqualNP.MetaComplexity.FanInTwo D ∧
      D.size + 1 ≤ C.size ∧ PEqualNP.NotBracket.notCount D ≤ PEqualNP.NotBracket.notCount C ∧
      ∀ j y, (D.wires (List.ofFn y)).getD (out j) false =
        (C.wires (List.ofFn (Function.update y i b))).getD (tap j) false := by
  have hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    exact ⟨by simpa using h1, h2⟩
  have hw : ∀ x, C.wires x = run C.gates x := fun _ => rfl
  let X : (Fin n → Bool) → List Bool := fun y => List.ofFn (Function.update y i b)
  have hXl : ∀ y, (X y).length = n := fun y => by simp [X]
  have hXi : ∀ y, (X y).getD i false = b := by
    intro y
    simp only [X]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp
  have hXk : ∀ (k : ℕ), k < n → k ≠ i → ∀ y, (X y).getD k false = (List.ofFn y).getD k false := by
    intro k hk hki y
    simp only [X]
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk),
      List.getElem_ofFn, List.getElem_ofFn]
    exact Function.update_of_ne (fun hc => hki (congrArg Fin.val hc)) _ _
  have hinw : ∀ k < n, ∀ y, (C.wires (X y)).getD k false = (X y).getD k false := by
    intro k hk y
    rw [hw]
    exact run_input _ _ _ (by rw [hXl]; exact hk)
  have hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin n → Bool),
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun k =>
          if k < n + j then (C.wires (X y)).getD k false else false) := by
    intro j hj y
    have h := run_gate C.gates (X y) j hj
    rw [hXl] at h
    exact h
  have hout (j : Fin q) : tap j < n + C.gates.length := by
    by_contra h
    apply hnc j
    refine ⟨false, fun y => ?_⟩
    change (C.wires (X y)).getD (tap j) false = false
    rw [hw]
    apply List.getD_eq_default
    rw [run_length, hXl]
    omega
  have hoi (j : Fin q) : tap j ≠ i := by
    intro h
    apply hnc j
    refine ⟨b, fun y => ?_⟩
    change (C.wires (X y)).getD (tap j) false = b
    rw [h, hinw i i.isLt]
    exact hXi y
  have hread : ∃ g ∈ C.gates, (i : ℕ) ∈ rds g := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j, x, y, hxy, hne⟩ := hess
    apply hne
    rw [hw, hw]
    refine indep i C.gates (fun g hg => (hops g hg).1) hcon _ _ (by simp) (fun k hk => ?_) _ (hoi j)
    by_cases h : k < n
    · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
        List.getElem_ofFn, List.getElem_ofFn]
      exact hxy _ fun hc => hk (congrArg Fin.val hc)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  obtain ⟨g, hg, hgi⟩ := hread
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
  let V := fun w y => (C.wires (X y)).getD w false
  obtain ⟨ds, S, legal, _, hs, hlen, hn, hV⟩ := restrict n n C.gates V hops (fun k hk => by
    by_cases h : k = i
    · exact Or.inl ⟨b, fun y => (hinw k hk y).trans (h ▸ hXi y)⟩
    · exact Or.inr ⟨k, hk, fun y => (hinw k hk y).trans (hXk k hk h y)⟩) hrec C.gates.length le_rfl
  have hkeep (j : Fin q) : ∃ k < n + ds.length, ∀ y, V (tap j) y = (run ds (List.ofFn y)).getD k false :=
    (hV (tap j) (hout j)).resolve_left (hnc j)
  choose out _ hOut using hkeep
  refine ⟨⟨ds, 0⟩, out, ?_, ?_, ?_, fun j y => (hOut j y).symm⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := legal g hg
    exact ⟨by simpa using h1, h2⟩
  · have hdrop : Drop n (fun w (y : Fin n → Bool) => (C.wires (X y)).getD w false) j := by
      obtain ⟨hop, hlen⟩ := hops _ hg
      have hv := hrec j hj
      have hii : ∀ y, (if (i : ℕ) < n + j then (C.wires (X y)).getD (i : ℕ) false else false) = b := by
        intro y
        rw [if_pos (by have := i.2; omega), hinw i i.2, hXi]
      generalize hI : C.gates[j].inputs = I at *
      generalize hO : C.gates[j].op = o at *
      have two : ∀ c : ℕ, (∀ y, (C.wires (X y)).getD (n + j) false =
          (b && if c < n + j then (C.wires (X y)).getD c false else false)) ∨
          (∀ y, (C.wires (X y)).getD (n + j) false =
          (b || if c < n + j then (C.wires (X y)).getD c false else false)) →
          Drop n (fun w (y : Fin n → Bool) => (C.wires (X y)).getD w false) j := by
        intro c hc
        by_cases hcl : c < n + j
        · simp only [hcl, if_true] at hc
          rcases hc with hc | hc <;> cases b
          · exact Or.inl ⟨false, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inr ⟨c, hcl, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inr ⟨c, hcl, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inl ⟨true, fun y => by simp only; rw [hc y]; rfl⟩
        · simp only [hcl, if_false] at hc
          rcases hc with hc | hc
          · exact Or.inl ⟨b && false, fun y => hc y⟩
          · exact Or.inl ⟨b || false, fun y => hc y⟩
      match I, hlen with
      | [], _ =>
        exfalso
        simp only [rds, hO, hI] at hgi
        rcases hop with rfl | rfl | rfl <;> simp at hgi
      | [a], _ =>
        have hai : a = i := by
          simp only [rds, hO, hI] at hgi
          rcases hop with rfl | rfl | rfl
          · exact (List.mem_singleton.1 hgi).symm
          · exact (List.mem_singleton.1 hgi).symm
          · exact (List.mem_singleton.1 hgi).symm
        subst hai
        refine Or.inl ⟨o.eval [b], fun y => ?_⟩
        simp only
        rw [hv y, List.map_singleton, hii y]
      | [a, c], _ =>
        rcases hop with rfl | rfl | rfl
        · have hac : (i : ℕ) = a ∨ (i : ℕ) = c := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          rcases hac with rfl | rfl
          · refine two c (Or.inl fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval]
          · refine two a (Or.inl fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval, Bool.and_comm]
        · have hac : (i : ℕ) = a ∨ (i : ℕ) = c := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          rcases hac with rfl | rfl
          · refine two c (Or.inr fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval]
          · refine two a (Or.inr fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval, Bool.or_comm]
        · have hai : (i : ℕ) = a := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          subst hai
          refine Or.inl ⟨!b, fun y => ?_⟩
          simp only
          rw [hv y, List.map_cons, hii y]
          rfl
    have hsub : S ⊆ (Finset.range C.gates.length).erase j := by
      intro k hk
      obtain ⟨h1, h2⟩ := hs k hk
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_range.2 h1⟩
      rintro rfl
      exact h2 hdrop
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 hj), Finset.card_range] at h1
    change ds.length + 1 ≤ C.gates.length
    omega
  · simpa [PEqualNP.NotBracket.notCount, countNot] using hn

end PEqualNP.Outside.L_meta_33687_aux


namespace PEqualNP.Outside.L_meta_33687_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Row (n : Nat) := Fin n → Bool

def Fits (b : Nat) {k q : Nat} (T : Fin q → Row k → Bool) (s : Nat) : Prop :=
  ∃ (C : Circuit) (tap : Fin q → Nat), FanInTwo C ∧ C.size ≤ s ∧
    PEqualNP.NotBracket.notCount C ≤ b ∧
    ∀ j x, (C.wires (List.ofFn x)).getD (tap j) false = T j x

def expandOn {n m : Nat} (π : Fin m → Fin n) (S : Finset (Fin m))
    (y : Row m) (i : Fin n) : Bool :=
  decide (∃ u, u ∉ S ∧ π u = i ∧ y u = true)

def embed {n m : Nat} (π : Fin m → Fin n) (r : Fin n → Fin m) (x : Row n) : Row m :=
  fun u => if r (π u) = u then x (π u) else false

theorem expand_embed {n m : Nat} (π : Fin m → Fin n) (r : Fin n → Fin m)
    (hr : ∀ i, π (r i) = i) (S : Finset (Fin m)) (hS : ∀ i, r i ∉ S) (x : Row n) :
    expandOn π S (embed π r x) = x := by
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [expandOn, decide_eq_true_eq]
  constructor
  · rintro ⟨u, _, hu, hx⟩
    by_cases h : r (π u) = u
    · have htrue : x (π u) = true := by simpa [embed,h] using hx
      exact hu ▸ htrue
    · simp [embed, h] at hx
  · intro hx
    exact ⟨r i, hS i, hr i, by simp [embed, hr, hx]⟩

theorem expand_update {n m : Nat} (π : Fin m → Fin n) (S : Finset (Fin m))
    (u : Fin m) (y : Row m) :
    expandOn π S (Function.update y u false) = expandOn π (insert u S) y := by
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [expandOn, decide_eq_true_eq]
  constructor
  · rintro ⟨v, hm, hp, hv⟩
    have hn : v ≠ u := by rintro rfl; simp at hv
    exact ⟨v, by simp [hm, hn], hp, by simpa [Function.update_of_ne hn] using hv⟩
  · rintro ⟨v, hm, hp, hv⟩
    have hn : v ≠ u := fun h => hm (Finset.mem_insert.mpr (Or.inl h))
    have hs : v ∉ S := fun h => hm (Finset.mem_insert.mpr (Or.inr h))
    exact ⟨v, hs, hp, by simpa [Function.update_of_ne hn] using hv⟩

theorem specialize {n m q b s : Nat} (C : Circuit) (tap : Fin q → Nat)
    (hC : FanInTwo C) (sz : C.size ≤ s) (nb : PEqualNP.NotBracket.notCount C ≤ b)
    (X : Row m → List Bool) (hX : ∀ y, (X y).length = n)
    (hin : ∀ i < n, Const (fun y => (X y).getD i false) ∨
      ∃ k < m, ∀ y, (X y).getD i false = (List.ofFn y).getD k false)
    (T : Fin q → Row m → Bool) (nonconst : ∀ j, ¬ Const (T j))
    (fits : ∀ j y, (C.wires (X y)).getD (tap j) false = T j y) : Fits b T s := by
  let V : Nat → Row m → Bool := fun w y => (C.wires (X y)).getD w false
  have hvalid (j : Fin q) : tap j < n + C.gates.length := by
    by_contra hn
    apply nonconst j
    refine ⟨false, fun y => (fits j y).symm.trans ?_⟩
    change (run C.gates (X y)).getD (tap j) false = false
    apply List.getD_eq_default
    rw [run_length, hX]; omega
  obtain ⟨ds, S, hg, _, hS, hl, hn, hs⟩ := restrict n m C.gates V
    (fun g h => ⟨by simpa using (hC g h).1, (hC g h).2⟩)
    (fun i hi => by
      have he (y : Row m) : V i y = (X y).getD i false :=
        run_input _ _ _ (by rw [hX]; exact hi)
      rcases hin i hi with ⟨c,hc⟩ | ⟨w, hw, heq⟩
      · exact Or.inl ⟨c, fun y => (he y).trans (hc y)⟩
      · exact Or.inr ⟨w, hw, fun y => (he y).trans (heq y)⟩)
    (fun j hj y => by
      have h := run_gate C.gates (X y) j hj
      rw [hX] at h
      exact h) C.gates.length le_rfl
  have ho (j : Fin q) : ∃ k < m + ds.length, ∀ y, T j y = (run ds (List.ofFn y)).getD k false := by
    rcases hs (tap j) (hvalid j) with ⟨c,hc⟩ | ⟨k,hk,hf⟩
    · exact (nonconst j ⟨c, fun y => (fits j y).symm.trans (hc y)⟩).elim
    · exact ⟨k,hk,fun y => (fits j y).symm.trans (hf y)⟩
  choose out _ hout using ho
  refine ⟨⟨ds,0⟩,out,?_,?_,?_,fun j y => (hout j y).symm⟩
  · intro g h
    exact ⟨by simpa using (hg g h).1, (hg g h).2⟩
  · have hsub : S ⊆ Finset.range C.gates.length := fun j hj => Finset.mem_range.mpr (hS j hj).1
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_range] at hh
    exact hl.trans (hh.trans sz)
  · have ht : countNot ds ≤ countNot C.gates := by simpa using hn
    exact ht.trans nb

theorem lower {n m q b s : Nat} (π : Fin m → Fin n) (F : Fin q → Row n → Bool)
    (sur : Function.Surjective π) (nc : ∀ j, ∃ x y, F j x ≠ F j y)
    (ess : ∀ i : Fin n, ∃ (j : Fin q) (x y : Row n),
      (∀ u, u ≠ i → x u = y u) ∧ F j x ≠ F j y)
    (hfit : Fits b (fun j y => F j (expandOn π ∅ y)) s) :
    m - n ≤ s ∧ Fits b F (s - (m - n)) := by
  classical
  choose r hr using sur
  let extras : Finset (Fin m) := Finset.univ \ Finset.univ.image r
  have hrx (i : Fin n) : r i ∉ extras := by simp [extras]
  have hcard : extras.card = m - n := by
    have inj : Function.Injective r := fun a d h => by simpa [hr] using congrArg π h
    rw [show extras = Finset.univ \ Finset.univ.image r from rfl, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [Finset.card_image_of_injective _ inj]
  obtain ⟨C,tap,hC,hsize,hnot,hval⟩ := hfit
  have step (S : Finset (Fin m)) (hs : S ⊆ extras) :
      ∃ (D : Circuit) (out : Fin q → Nat), FanInTwo D ∧ D.size + S.card ≤ s ∧
        PEqualNP.NotBracket.notCount D ≤ b ∧
        ∀ j y, (D.wires (List.ofFn y)).getD (out j) false = F j (expandOn π S y) := by
    induction S using Finset.induction_on with
    | empty => exact ⟨C,tap,hC,by simpa using hsize,hnot,hval⟩
    | @insert u S hnotin ih =>
      have hs' : S ⊆ extras := (Finset.subset_insert _ _).trans hs
      obtain ⟨D,out,hD,sz,nb,hout⟩ := ih hs'
      let r' : Fin n → Fin m := fun i => if i = π u then u else r i
      have hr' (i : Fin n) : π (r' i) = i := by by_cases h : i = π u <;> simp [r',h,hr]
      have hrs (i : Fin n) : r' i ∉ S := by
        by_cases h : i = π u
        · simpa [r',h] using hnotin
        · simpa [r',h] using (fun hS : r i ∈ S => hrx i (hs' hS))
      have hn (j : Fin q) : ¬ Const (fun y : Row m =>
          (D.wires (List.ofFn (Function.update y u false))).getD (out j) false) := by
        rintro ⟨c,hc⟩
        obtain ⟨x,y,hxy⟩ := nc j
        apply hxy
        have h (z : Row n) : F j z = c := by
          simpa only [hout, expand_update, expand_embed π r hr (insert u S) (fun i hi => hrx i (hs hi))] using hc (embed π r z)
        rw [h x,h y]
      obtain ⟨j,x,y,hxy,he⟩ := ess (π u)
      have dep : ∃ (j : Fin q) (x y : Row m), (∀ k, k ≠ u → x k = y k) ∧
        (D.wires (List.ofFn x)).getD (out j) false ≠ (D.wires (List.ofFn y)).getD (out j) false := by
        refine ⟨j, embed π r' x, embed π r' y, ?_, ?_⟩
        · intro k hk
          by_cases hp : π k = π u
          · simp [embed, r',hp, Ne.symm hk]
          · simp [embed,hxy _ hp]
        · simpa only [hout, expand_embed π r' hr' S hrs] using he
      obtain ⟨E,t,hE,hsz,hnc,hq⟩ := one_drop m q D out hD u false dep hn
      refine ⟨E,t,hE,?_,hnc.trans nb,fun j y => ?_⟩
      · rw [Finset.card_insert_of_notMem hnotin]; omega
      · rw [hq, hout, expand_update]
  obtain ⟨D,out,hD,sz,nb,hm⟩ := step extras (by rfl)
  rw [hcard] at sz
  refine ⟨by omega, ?_⟩
  have dns : ∀ j, ¬ Const (F j) := by
    intro j h; obtain ⟨c,hc⟩ := h
    obtain ⟨x,y,hxy⟩ := nc j
    exact hxy ((hc x).trans (hc y).symm)
  refine specialize (n := m) (m := n) (s := s - (m - n)) D out hD (by omega) nb (fun x => List.ofFn (embed π r x))
    (by simp) (fun u hu => ?_) F dns (fun j y => ?_)
  · let v : Fin m := ⟨u,hu⟩
    by_cases hv : r (π v) = v
    · refine Or.inr ⟨π v, (π v).isLt, fun y => ?_⟩
      rw [List.getD_eq_getElem _ _ (by simpa), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, List.getElem_ofFn]
      simp [embed, hv, v]
    · refine Or.inl ⟨false, fun y => ?_⟩
      change (List.ofFn (embed π r y)).getD u false = false
      rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_ofFn]
      simp [embed, hv, v]
  · rw [hm, expand_embed π r hr extras hrx]

end PEqualNP.Outside.L_meta_33687_aux


namespace PEqualNP.Outside.L_meta_33687_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The wire remapping argument follows rifter0418, L-meta-18804, PR 23417.
def wireName {n : Nat} (r : Fin n → Nat) (base i : Nat) : Nat :=
  if h : i < n then r ⟨i,h⟩ else base + (i - n)

def renameGate {n : Nat} (r : Fin n → Nat) (base : Nat) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (wireName r base)⟩

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem lookup {n : Nat} (r : Fin n → Nat) (W : List Bool)
    (bounds : ∀ i, r i < W.length) (x : Row n)
    (agree : ∀ i, W.getD (r i) false = x i) (z : List Bool) (i : Nat) :
    (W ++ z).getD (wireName r W.length i) false = (List.ofFn x ++ z).getD i false := by
  unfold wireName
  split
  next hi =>
    rw [List.getD_append _ _ _ _ (bounds ⟨i,hi⟩),List.getD_append _ _ _ _ (by simpa)]
    rw [agree, List.getD_eq_getElem _ _ (by simpa), List.getElem_ofFn]
  next hi =>
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : W.length ≤ W.length + (i - n)),
      List.getElem?_append_right (by simp; omega : (List.ofFn x).length ≤ i),
      List.length_ofFn, Nat.add_sub_cancel_left]

theorem simulation {n : Nat} (r : Fin n → Nat) (W : List Bool)
    (bounds : ∀ i, r i < W.length) (x : Row n)
    (agree : ∀ i, W.getD (r i) false = x i) (gs : List Gate) (z : List Bool) :
    ∃ endBits, run gs (List.ofFn x ++ z) = List.ofFn x ++ endBits ∧
      run (gs.map (renameGate r W.length)) (W ++ z) = W ++ endBits := by
  induction gs generalizing z with
  | nil => exact ⟨z,rfl,rfl⟩
  | cons g gs ih =>
    let bit := g.op.eval (g.inputs.map fun i => (List.ofFn x ++ z).getD i false)
    obtain ⟨t,h1,h2⟩ := ih (z ++ [bit])
    refine ⟨t,?_,?_⟩
    · simpa [run,bit,List.append_assoc] using h1
    · have hstep : wireStep (W ++ z) (renameGate r W.length g) = W ++ (z ++ [bit]) := by
        simp only [wireStep,renameGate,List.map_map,Function.comp_def,
          lookup r W bounds x agree,List.append_assoc,bit]
      change run _ (wireStep (W ++ z) (renameGate r W.length g)) = _
      rw [hstep]; exact h2

theorem rename_value {n : Nat} (r : Fin n → Nat) (W : List Bool)
    (bounds : ∀ i, r i < W.length) (x : Row n)
    (agree : ∀ i, W.getD (r i) false = x i) (gs : List Gate) (j : Nat) :
    (run (gs.map (renameGate r W.length)) W).getD (wireName r W.length j) false =
      (run gs (List.ofFn x)).getD j false := by
  obtain ⟨z,h1,h2⟩ := simulation r W bounds x agree gs []
  simp only [List.append_nil] at h1 h2
  rw [h1,h2,lookup _ _ bounds x agree]

theorem countNot_map {n : Nat} (r : Fin n → Nat) (base : Nat) (gs : List Gate) :
    countNot (gs.map (renameGate r base)) = countNot gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : g.op = GateOp.not <;> simp [countNot,renameGate,h,countNot] at ih ⊢ <;> omega

def bundle {n m : Nat} (π : Fin m → Fin n) (r : Fin n → Fin m)
    (S : Finset (Fin m)) (y : Row m) (i : Fin n) : Bool :=
  decide (∃ u, π u = i ∧ (u = r i ∨ u ∈ S) ∧ y u = true)

theorem bundle_empty {n m : Nat} (π : Fin m → Fin n) (r : Fin n → Fin m)
    (hr : ∀ i, π (r i) = i) (y : Row m) (i : Fin n) : bundle π r ∅ y i = y (r i) := by
  apply Bool.eq_iff_iff.mpr
  simp [bundle,hr]

theorem bundle_insert {n m : Nat} (π : Fin m → Fin n) (r : Fin n → Fin m)
    (S : Finset (Fin m)) (u : Fin m) (y : Row m) (i : Fin n) :
    bundle π r (insert u S) y i = (bundle π r S y i || (decide (π u = i) && y u)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bundle, decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true, Finset.mem_insert]
  constructor
  · rintro ⟨v, hp, hv | hv | hv, h⟩
    · exact Or.inl ⟨v,hp,Or.inl hv,h⟩
    · subst v; exact Or.inr ⟨hp,h⟩
    · exact Or.inl ⟨v,hp,Or.inr hv,h⟩
  · rintro (⟨v,hp,hv | hv,h⟩ | ⟨hp,h⟩)
    · exact ⟨v,hp,Or.inl hv,h⟩
    · exact ⟨v,hp,Or.inr (Or.inr hv),h⟩
    · exact ⟨u,hp,Or.inr (Or.inl rfl),h⟩

theorem make_prefix {n m : Nat} (π : Fin m → Fin n) (r : Fin n → Fin m)
    (hr : ∀ i, π (r i) = i) (S : Finset (Fin m)) :
    ∃ (gs : List Gate) (t : Fin n → Nat), gs.length = S.card ∧
      (∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length = 2) ∧
      (∀ i, t i < m + gs.length) ∧
      ∀ y i, (run gs (List.ofFn y)).getD (t i) false = bundle π r S y i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨[],fun i => r i,by simp,by simp,fun i => by simpa using (r i).isLt,?_⟩
    intro y i
    rw [bundle_empty π r hr]
    change (List.ofFn y).getD (r i) false = y (r i)
    rw [List.getD_eq_getElem _ _ (by simpa using (r i).isLt), List.getElem_ofFn]
  | @insert u S hu ih =>
    obtain ⟨gs,t,hl,hg,ht,hv⟩ := ih
    let g : Gate := ⟨GateOp.or,[t (π u),u]⟩
    let t' : Fin n → Nat := fun i => if i = π u then m + gs.length else t i
    refine ⟨gs ++ [g],t',?_,?_,?_,?_⟩
    · rw [Finset.card_insert_of_notMem hu]; simp [hl]
    · intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact hg a h
      · rw [List.mem_singleton.mp h]; simp [g]
    · intro i; by_cases hi : i = π u
      · simp [t',hi]
      · simp only [t',hi,ite_false,List.length_append,List.length_singleton]
        have := ht i
        omega
    · intro y i
      have hh : (run gs (List.ofFn y)).length = m + gs.length := by simp [run_length]
      by_cases hi : i = π u
      · subst i
        have hval : (run gs (List.ofFn y)).getD u false = y u := by
          rw [run_input _ _ _ (by simpa using u.isLt),
            List.getD_eq_getElem _ _ (by simpa using u.isLt), List.getElem_ofFn]
        rw [bundle_insert,run_snoc]
        simp only [t', if_pos rfl]
        rw [← hh,getD_at]
        simp only [g,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false]
        rw [hv,hval]
        simp
      · rw [bundle_insert,run_snoc]
        simp only [t',if_neg hi]
        rw [getD_lt _ _ _ (by rw [hh]; exact ht i),hv]
        simp [Ne.symm hi]

theorem upper {n m q b s : Nat} (π : Fin m → Fin n) (F : Fin q → Row n → Bool)
    (sur : Function.Surjective π) (fit : Fits b F s) :
    Fits b (fun j y => F j (expandOn π ∅ y)) (s + (m - n)) := by
  classical
  choose r hr using sur
  let extras : Finset (Fin m) := Finset.univ \ Finset.univ.image r
  have hcard : extras.card = m - n := by
    have inj : Function.Injective r := fun a d h => by simpa [hr] using congrArg π h
    rw [show extras = Finset.univ \ Finset.univ.image r from rfl, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [Finset.card_image_of_injective _ inj]
  have total (y : Row m) : bundle π r extras y = expandOn π ∅ y := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [bundle,expandOn,decide_eq_true_eq]
    constructor
    · rintro ⟨u,hp,_,hy⟩; exact ⟨u,by simp,hp,hy⟩
    · rintro ⟨u,_,hp,hy⟩
      refine ⟨u,hp,?_,hy⟩
      by_cases he : u ∈ Finset.univ.image r
      · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp he
        have hji : j = i := (hr j).symm.trans ((congrArg π hj).trans hp)
        exact Or.inl (hji ▸ hj.symm)
      · exact Or.inr (by simp [extras,he])
  obtain ⟨gs,t,hl,hg,ht,hv⟩ := make_prefix π r hr extras
  obtain ⟨C,tap,hC,sz,nb,hval⟩ := fit
  let base := m + gs.length
  let D : Circuit := ⟨gs ++ C.gates.map (renameGate t base),0⟩
  refine ⟨D,fun j => wireName t base (tap j),?_,?_,?_,fun j y => ?_⟩
  · intro g hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨h,l⟩ := hg g hm
      exact ⟨by simp [h],by omega⟩
    · obtain ⟨g',hg',eg⟩ := List.mem_map.mp hm
      subst g
      simpa [renameGate] using hC g' hg'
  · have hl' := hl.trans hcard
    change (gs ++ C.gates.map (renameGate t base)).length ≤ _
    have hc : C.gates.length ≤ s := sz
    simp only [List.length_append,List.length_map,hl']
    omega
  · have hzero : countNot gs = 0 := by
      unfold countNot
      rw [List.length_eq_zero_iff]
      apply List.filter_eq_nil_iff.mpr
      intro g hm
      simp [(hg g hm).1]
    change countNot (gs ++ C.gates.map (renameGate t base)) ≤ b
    rw [countNot_append,countNot_map,hzero,zero_add]
    exact nb
  · let W := run gs (List.ofFn y)
    have hW : W.length = base := by simp [W,base,run_length]
    have hv' (i : Fin n) : W.getD (t i) false = expandOn π ∅ y i := (hv y i).trans (congrFun (total y) i)
    have eq := rename_value t W (fun i => by rw [hW]; exact ht i) (expandOn π ∅ y) hv' C.gates (tap j)
    rw [hW] at eq
    have hrun : run (gs ++ C.gates.map (renameGate t base)) (List.ofFn y) =
        run (C.gates.map (renameGate t base)) W := by simp [run, W, List.foldl_append]
    change (run (gs ++ C.gates.map (renameGate t base)) (List.ofFn y)).getD _ false = _
    rw [hrun]
    exact eq.trans (hval j _)

end PEqualNP.Outside.L_meta_33687_aux

open PEqualNP.Outside.L_meta_33687_aux in
theorem PEqualNP.Outside.L_meta_33687 :
  ∀ (n m q b : Nat) (π : Fin m → Fin n) (F : Fin q → (Fin n → Bool) → Bool),
  Function.Surjective π →
  (∀ j, ∃ x y, F j x ≠ F j y) →
  (∀ i : Fin n, ∃ (j : Fin q) (x y : Fin n → Bool), (∀ u, u ≠ i → x u = y u) ∧ F j x ≠ F j y) →
  let expand := fun (y : Fin m → Bool) (i : Fin n) => decide (∃ u, π u = i ∧ y u = true)
  let fits := fun (k : Nat) (T : Fin q → (Fin k → Bool) → Bool) (s : Nat) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
      PEqualNP.NotBracket.notCount C ≤ b ∧
      ∀ j x, (C.wires (List.ofFn x)).getD (tap j) false = T j x
  let lifted := fun j y => F j (expand y)
  (∀ s, fits m lifted s → m-n ≤ s) ∧
  ∀ s, fits n F s ↔ fits m lifted (s+(m-n)) := by
  intro n m q b π F sur nc ess
  let T : Fin q → Row m → Bool := fun j y => F j (expandOn π ∅ y)
  have h : (∀ s, Fits b T s → m - n ≤ s) ∧
      ∀ s, Fits b F s ↔ Fits b T (s + (m - n)) := by
    refine ⟨fun s hf => (lower π F sur nc ess hf).1, fun s => ⟨upper π F sur, ?_⟩⟩
    intro x
    simpa using (lower π F sur nc ess x).2
  have eq (y : Row m) : expandOn π ∅ y = fun i => decide (∃ u, π u = i ∧ y u = true) := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [expandOn, decide_eq_true_eq]
    constructor
    · rintro ⟨u, _, hu, hy⟩
      exact ⟨u, hu, hy⟩
    · rintro ⟨u, hu, hy⟩
      exact ⟨u, by simp, hu, hy⟩
  simpa only [Fits, T, eq] using h
