import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1322_aux

open PEqualNP.CircuitLowerBounds

private theorem notCount_eq_filter_range [DecidableEq GateOp] (C : Circuit) :
    ((List.range C.size).filter (fun u =>
      decide ((C.gates.getD u ⟨GateOp.or, []⟩).op = .not))).length =
    PEqualNP.NotBracket.notCount C := by
  dsimp only [PEqualNP.NotBracket.notCount, Circuit.size]
  suffices h : ((List.range C.gates.length).filter (fun u =>
      decide ((C.gates.getD u ⟨GateOp.or, []⟩).op = .not))).length =
      (C.gates.filter (fun g => decide (g.op = .not))).length by
    rw [h]
    congr 1
    apply List.filter_congr
    intro g _
    exact congrArg (@decide (g.op = .not)) (Subsingleton.elim _ _)
  induction C.gates using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
      List.filter_append, List.length_append, List.length_append]
    have ha : (List.range gs.length).filter (fun u =>
        decide (((gs ++ [g]).getD u ⟨.or, []⟩).op = .not)) =
        (List.range gs.length).filter (fun u => decide ((gs.getD u ⟨.or, []⟩).op = .not)) := by
      apply List.filter_congr
      intro u hu
      have hlt := List.mem_range.mp hu
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
    have hb : ([gs.length].filter (fun u =>
        decide (((gs ++ [g]).getD u ⟨.or, []⟩).op = .not))).length =
        ([g].filter (fun g' => decide (g'.op = .not))).length := by
      have hgd : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
      cases h : g.op <;> simp [hgd, h]
    rw [ha, ih, hb]

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

private theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (ht : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]

private theorem getD_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp

private theorem run_prefix (gs1 gs2 : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs1.length) :
    (run (gs1 ++ gs2) x).getD w false = (run gs1 x).getD w false := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc, run_snoc, getD_lt]
    · exact ih
    · rw [run_length, List.length_append]; omega

private theorem run_input (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  simpa [run] using run_prefix [] gs x w (by simpa using hw)

private theorem run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < x.length + j then (run gs x).getD i false else false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := (List.take_append_drop j gs).symm
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa [List.append_assoc] using h1
  have hlen : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hp1 : (run gs x).getD (x.length + j) false =
      (run (gs.take j ++ [gs[j]]) x).getD (x.length + j) false := by
    conv_lhs => rw [hsplit]
    exact run_prefix (gs.take j ++ [gs[j]]) (gs.drop (j + 1)) x (x.length + j)
      (by rw [List.length_append, List.length_singleton, hlen]; omega)
  rw [hp1, run_snoc]
  have hrlen : (run (gs.take j) x).length = x.length + j := by rw [run_length, hlen]
  rw [← hrlen, getD_eq]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [hrlen]
  by_cases hi : i < x.length + j
  · rw [if_pos hi]
    have htake : (run gs x).getD i false = (run (gs.take j) x).getD i false := by
      conv_lhs => rw [hsplit, List.append_assoc]
      exact run_prefix (gs.take j) ([gs[j]] ++ gs.drop (j + 1)) x i (by rw [hlen]; exact hi)
    exact htake.symm
  · rw [if_neg hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

private theorem sigPrefix_bound [DecidableEq GateOp] (C : Circuit) (f : ℕ → Bool) :
    ∀ m, ((List.range m).filter (fun u =>
      decide ((C.gates.getD u ⟨.or, []⟩).op = .not))).foldl
      (fun v u => 2 * v + (if f u then 1 else 0)) 0 <
      2 ^ ((List.range m).filter (fun u =>
        decide ((C.gates.getD u ⟨.or, []⟩).op = .not))).length := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append]
    by_cases hnot : (C.gates.getD m ⟨.or, []⟩).op = .not
    · have h1 : [m].filter (fun u => decide ((C.gates.getD u ⟨.or, []⟩).op = .not)) = [m] := by
        rw [List.filter_cons, List.filter_nil, if_pos (decide_eq_true hnot)]
      rw [h1, List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append, List.length_singleton, Nat.pow_succ]
      cases hfm : f m <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    · have h1 : [m].filter (fun u => decide ((C.gates.getD u ⟨.or, []⟩).op = .not)) = [] := by
        rw [List.filter_cons, List.filter_nil, if_neg (by rw [decide_eq_true_eq]; exact hnot)]
      rw [h1, List.append_nil]
      exact ih

private theorem sigPrefix_mono [DecidableEq GateOp] (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hrb : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + 2 + j)
    (X Y : Finset (Fin n)) (hXY : X ⊆ Y) :
    let wire := fun (Z : Finset (Fin n)) (u : ℕ) =>
      (run C.gates (List.ofFn (fun a : Fin n => decide (a ∈ Z)) ++ [false, true])).getD u false
    let sigP := fun (Z : Finset (Fin n)) (m : ℕ) =>
      ((List.range m).filter (fun u => decide ((C.gates.getD u ⟨.or, []⟩).op = .not))).foldl
        (fun v u => 2 * v + (if wire Z (n + 2 + u) then 1 else 0)) 0
    ∀ m ≤ C.size, sigP Y m ≤ sigP X m ∧
      (sigP Y m = sigP X m → ∀ w < n + 2 + m, wire X w = true → wire Y w = true) := by
  intro wire sigP m hm
  induction m with
  | zero =>
    refine ⟨le_rfl, fun _ w hw hwx => ?_⟩
    have hlenX : (List.ofFn (fun a : Fin n => decide (a ∈ X)) ++ [false, true]).length = n + 2 := by simp
    have hlenY : (List.ofFn (fun a : Fin n => decide (a ∈ Y)) ++ [false, true]).length = n + 2 := by simp
    dsimp only [wire] at hwx ⊢
    rw [run_input C.gates _ w (by rw [hlenX]; exact hw)] at hwx
    rw [run_input C.gates _ w (by rw [hlenY]; exact hw)]
    rcases Nat.lt_or_ge w n with hwn | hwn
    · have h1 : (List.ofFn (fun a : Fin n => decide (a ∈ X)) ++ [false, true]).getD w false =
          decide (⟨w, hwn⟩ ∈ X) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hwn]),
          List.getElem?_ofFn, dif_pos hwn]; rfl
      have h2 : (List.ofFn (fun a : Fin n => decide (a ∈ Y)) ++ [false, true]).getD w false =
          decide (⟨w, hwn⟩ ∈ Y) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hwn]),
          List.getElem?_ofFn, dif_pos hwn]; rfl
      rw [h1] at hwx; rw [h2]
      exact decide_eq_true (hXY (of_decide_eq_true hwx))
    · have hw' : w = n ∨ w = n + 1 := by omega
      rcases hw' with hweq | hweq
      · have h1 : (List.ofFn (fun a : Fin n => decide (a ∈ X)) ++ [false, true]).getD w false = false := by
          rw [hweq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
        rw [h1] at hwx; cases hwx
      · rw [hweq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
  | succ m ih =>
    obtain ⟨hle, heq_imp⟩ := ih (by omega)
    have hmlt : m < C.gates.length := hm
    have hg_eq : C.gates.getD m ⟨.or, []⟩ = C.gates[m] := List.getD_eq_getElem C.gates _ hmlt
    have hlenX : (List.ofFn (fun a : Fin n => decide (a ∈ X)) ++ [false, true]).length = n + 2 := by simp
    have hlenY : (List.ofFn (fun a : Fin n => decide (a ∈ Y)) ++ [false, true]).length = n + 2 := by simp
    have hx_gate := run_gate C.gates (List.ofFn (fun a : Fin n => decide (a ∈ X)) ++ [false, true]) m hmlt
    have hy_gate := run_gate C.gates (List.ofFn (fun a : Fin n => decide (a ∈ Y)) ++ [false, true]) m hmlt
    rw [hlenX] at hx_gate
    rw [hlenY] at hy_gate
    by_cases hnot : C.gates[m].op = .not
    · have hflt : [m].filter (fun u => decide ((C.gates.getD u ⟨.or, []⟩).op = .not)) = [m] := by
        rw [List.filter_cons, List.filter_nil, if_pos (decide_eq_true ((congrArg Gate.op hg_eq).trans hnot))]
      have hsX : sigP X (m + 1) = 2 * sigP X m + (if wire X (n + 2 + m) then 1 else 0) := by
        dsimp only [sigP]
        rw [List.range_succ, List.filter_append, hflt, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hsY : sigP Y (m + 1) = 2 * sigP Y m + (if wire Y (n + 2 + m) then 1 else 0) := by
        dsimp only [sigP]
        rw [List.range_succ, List.filter_append, hflt, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hsX, hsY]
      rcases lt_or_eq_of_le hle with hlt | heq
      · refine ⟨by split_ifs <;> omega, fun heq' => by exfalso; split_ifs at heq' <;> omega⟩
      · have hmon := heq_imp heq
        have hanti : wire Y (n + 2 + m) = true → wire X (n + 2 + m) = true := by
          intro hy
          dsimp only [wire] at hy ⊢
          rw [hy_gate, hnot] at hy
          rw [hx_gate, hnot]
          rcases hin : C.gates[m].inputs with _ | ⟨a, rest⟩
          · simp [GateOp.eval]
          · have ha : a < n + 2 + m := hrb m hmlt a (by rw [hin]; simp)
            rw [hin] at hy
            simp only [List.map_cons, GateOp.eval, List.headD_cons, if_pos ha] at hy ⊢
            cases hxa : (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ X)) ++ [false, true])).getD a false
            · rfl
            · have hy_true : (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ Y)) ++ [false, true])).getD a false = true :=
                hmon a ha hxa
              rw [hy_true] at hy; simp at hy
        have hle_b : (if wire Y (n + 2 + m) then 1 else 0) ≤ (if wire X (n + 2 + m) then 1 else 0) := by
          cases hxb : wire X (n + 2 + m) <;> cases hyb : wire Y (n + 2 + m)
          · exact le_rfl
          · exfalso; have := hanti hyb; rw [hxb] at this; cases this
          · decide
          · exact le_rfl
        refine ⟨by omega, fun heq' w hw hwx => ?_⟩
        rcases Nat.lt_or_eq_of_le (show w ≤ n + 2 + m by omega) with hwlt | rfl
        · exact hmon w hwlt hwx
        · have heq_b : (if wire Y (n + 2 + m) then 1 else 0) = (if wire X (n + 2 + m) then 1 else 0) := by omega
          cases hxb : wire X (n + 2 + m) <;> cases hyb : wire Y (n + 2 + m)
          · rw [hxb] at hwx; cases hwx
          · rfl
          · simp [hxb, hyb] at heq_b
          · rfl
    · have hflt : [m].filter (fun u => decide ((C.gates.getD u ⟨.or, []⟩).op = .not)) = [] := by
        rw [List.filter_cons, List.filter_nil, if_neg (by rw [hg_eq]; simp [hnot])]
      have hsX : sigP X (m + 1) = sigP X m := by
        dsimp only [sigP]; rw [List.range_succ, List.filter_append, hflt, List.append_nil]
      have hsY : sigP Y (m + 1) = sigP Y m := by
        dsimp only [sigP]; rw [List.range_succ, List.filter_append, hflt, List.append_nil]
      rw [hsX, hsY]
      refine ⟨hle, fun heq w hw hwx => ?_⟩
      have hmon := heq_imp heq
      rcases Nat.lt_or_eq_of_le (show w ≤ n + 2 + m by omega) with hwlt | rfl
      · exact hmon w hwlt hwx
      · dsimp only [wire] at hwx ⊢
        rw [hx_gate] at hwx; rw [hy_gate]
        have hop : C.gates[m].op = .and ∨ C.gates[m].op = .or := by
          rcases (hfan _ (List.getElem_mem hmlt)).1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hnot
        rcases hop with hand | hor
        · rw [hand] at hwx ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at hwx ⊢
          intro a ha
          have halt := hrb m hmlt a ha
          rw [if_pos halt]
          have hwx_a := hwx a ha
          rw [if_pos halt] at hwx_a
          exact hmon a halt hwx_a
        · rw [hor] at hwx ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_def, id_eq] at hwx ⊢
          obtain ⟨a, ha, hax⟩ := hwx
          have halt := hrb m hmlt a ha
          rw [if_pos halt] at hax
          exact ⟨a, ha, by rw [if_pos halt]; exact hmon a halt hax⟩

private theorem rise_fall_balance (f : ℕ → Bool) (l : ℕ) :
    let R := ((Finset.range l).filter (fun t => f t = false ∧ f (t + 1) = true)).card
    let F := ((Finset.range l).filter (fun t => f t = true ∧ f (t + 1) = false)).card
    if f l = true then R ≤ F + 1 ∧ F ≤ R else R ≤ F ∧ F ≤ R + 1 := by
  induction l with
  | zero =>
    simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty]
    cases f 0 <;> simp
  | succ l ih =>
    dsimp only at ih ⊢
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    have hnr : l ∉ (Finset.range l).filter (fun t => f t = false ∧ f (t + 1) = true) := by simp
    have hnf : l ∉ (Finset.range l).filter (fun t => f t = true ∧ f (t + 1) = false) := by simp
    cases hfl : f l <;> cases hfl1 : f (l + 1) <;>
      simp only [hfl, hfl1, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
        Finset.card_insert_of_notMem hnr, Finset.card_insert_of_notMem hnf] at ih ⊢ <;> omega

private theorem rise_le_fall_add_one (f : ℕ → Bool) (l : ℕ) :
    ((Finset.range l).filter (fun t => f t = false ∧ f (t + 1) = true)).card ≤
    ((Finset.range l).filter (fun t => f t = true ∧ f (t + 1) = false)).card + 1 := by
  have h := rise_fall_balance f l
  dsimp only at h
  cases hfl : f l <;> simp only [hfl, ↓reduceIte, Bool.false_eq_true] at h <;> omega

private theorem mono_chain_set (n l : ℕ) (P : ℕ → Finset (Fin n))
    (hx : ∀ t < l, P t ⊆ P (t + 1)) (t1 t2 : ℕ) (h12 : t1 ≤ t2) (h2l : t2 ≤ l) :
    P t1 ⊆ P t2 := by
  induction h12 with
  | refl => exact Finset.Subset.rfl
  | @step m h1m ih => exact (ih (by omega)).trans (hx m (by omega))

private theorem nat_le_two_pow (d : ℕ) : 1 + d ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih => rw [Nat.pow_succ]; omega

private theorem gate_fall_and (s : Finset ℕ)
    (l : List ℕ) (f : ℕ → ℕ → Bool) :
    (s.filter (fun p => (l.map (f p)).all id = true ∧ (l.map (f (p + 1))).all id = false)).card ≤
      (l.dedup.map (fun a => (s.filter (fun p => f p a = true ∧ f (p + 1) a = false)).card)).sum := by
  have hsub : s.filter (fun p => (l.map (f p)).all id = true ∧ (l.map (f (p + 1))).all id = false) ⊆
      l.dedup.toFinset.biUnion (fun a => s.filter (fun p => f p a = true ∧ f (p + 1) a = false)) := by
    intro p hp
    obtain ⟨hps, h1, h2⟩ := Finset.mem_filter.mp hp
    simp only [List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h1
    have h2' : ∃ a ∈ l, f (p + 1) a = false := by
      by_contra hall
      push_neg at hall
      have htrue : (l.map (f (p + 1))).all id = true := by
        simp only [List.all_map, List.all_eq_true, Function.comp_def, id_eq]
        intro a ha
        cases hfa : f (p + 1) a
        · exact absurd hfa (hall a ha)
        · rfl
      rw [htrue] at h2; cases h2
    obtain ⟨a, ha, hfa⟩ := h2'
    exact Finset.mem_biUnion.mpr ⟨a, List.mem_toFinset.mpr (List.mem_dedup.mpr ha),
      Finset.mem_filter.mpr ⟨hps, h1 a ha, hfa⟩⟩
  calc (s.filter (fun p => (l.map (f p)).all id = true ∧ (l.map (f (p + 1))).all id = false)).card
      ≤ (l.dedup.toFinset.biUnion (fun a => s.filter (fun p => f p a = true ∧ f (p + 1) a = false))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ a ∈ l.dedup.toFinset, (s.filter (fun p => f p a = true ∧ f (p + 1) a = false)).card :=
        Finset.card_biUnion_le
    _ = (l.dedup.map (fun a => (s.filter (fun p => f p a = true ∧ f (p + 1) a = false)).card)).sum := by
        rw [List.sum_toFinset _ (List.nodup_dedup l)]

private theorem gate_fall_or (s : Finset ℕ)
    (l : List ℕ) (f : ℕ → ℕ → Bool) :
    (s.filter (fun p => (l.map (f p)).any id = true ∧ (l.map (f (p + 1))).any id = false)).card ≤
      (l.dedup.map (fun a => (s.filter (fun p => f p a = true ∧ f (p + 1) a = false)).card)).sum := by
  have hsub : s.filter (fun p => (l.map (f p)).any id = true ∧ (l.map (f (p + 1))).any id = false) ⊆
      l.dedup.toFinset.biUnion (fun a => s.filter (fun p => f p a = true ∧ f (p + 1) a = false)) := by
    intro p hp
    obtain ⟨hps, h1, h2⟩ := Finset.mem_filter.mp hp
    simp only [List.any_map, List.any_eq_true, Function.comp_def, id_eq] at h1
    obtain ⟨a, ha, hfa⟩ := h1
    have hfa2 : f (p + 1) a = false := by
      by_contra hne
      have ht : f (p + 1) a = true := by cases hf : f (p + 1) a <;> simp_all
      have hany : (l.map (f (p + 1))).any id = true := by
        simp only [List.any_map, List.any_eq_true, Function.comp_def, id_eq]
        exact ⟨a, ha, ht⟩
      rw [hany] at h2; cases h2
    exact Finset.mem_biUnion.mpr ⟨a, List.mem_toFinset.mpr (List.mem_dedup.mpr ha),
      Finset.mem_filter.mpr ⟨hps, hfa, hfa2⟩⟩
  calc (s.filter (fun p => (l.map (f p)).any id = true ∧ (l.map (f (p + 1))).any id = false)).card
      ≤ (l.dedup.toFinset.biUnion (fun a => s.filter (fun p => f p a = true ∧ f (p + 1) a = false))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ a ∈ l.dedup.toFinset, (s.filter (fun p => f p a = true ∧ f (p + 1) a = false)).card :=
        Finset.card_biUnion_le
    _ = (l.dedup.map (fun a => (s.filter (fun p => f p a = true ∧ f (p + 1) a = false)).card)).sum := by
        rw [List.sum_toFinset _ (List.nodup_dedup l)]

private theorem peel_chain (n t k l : ℕ) (P : ℕ → Finset (Fin n)) (hP : ∀ p < k, P p ⊆ P (p + 1))
    (C : Circuit) (tap : Fin t → ℕ)
    (hfan : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hrb : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + 2 + j)
    (htap : ∀ a : Fin t, tap a < n + 2 + C.size)
    (hnotc : PEqualNP.NotBracket.notCount C = l)
    (hchg_cov : ∀ p < k, ∃ a : Fin t,
      (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ P p)) ++ [false, true])).getD (tap a) false ≠
      (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ P (p + 1))) ++ [false, true])).getD (tap a) false) :
    let wire := fun (p u : ℕ) =>
      (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ P p)) ++ [false, true])).getD u false
    let falls := fun (u : ℕ) =>
      ((Finset.range k).filter (fun p => wire p u = true ∧ wire (p + 1) u = false)).card
    k ≤ C.size - l + t ∧
      (∑ a : Fin t, falls (tap a)) ≤ l * 2 ^ (C.size - l + t - k) := by
  intro wire falls
  let _ : DecidableEq GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  let chg : ℕ → Finset ℕ := fun u => (Finset.range k).filter (fun p => wire p u ≠ wire (p + 1) u)
  have hlenX : ∀ p, (List.ofFn (fun i : Fin n => decide (i ∈ P p)) ++ [false, true]).length = n + 2 := by
    intro p; simp
  have hpos_count : ((C.gates.take C.size).filter (fun g => decide (g.op ≠ .not))).length = C.size - l := by
    dsimp only [Circuit.size]
    rw [List.take_length]
    have hsplit : ∀ (L : List Gate),
        (L.filter (fun g => decide (g.op ≠ .not))).length +
        (L.filter (fun g => decide (g.op = .not))).length = L.length := by
      intro L
      induction L with
      | nil => simp
      | cons g gs ih =>
        by_cases h : g.op = .not
        · have h1 : decide (g.op ≠ .not) = false := decide_eq_false (not_not.mpr h)
          have h2 : decide (g.op = .not) = true := decide_eq_true h
          rw [List.filter_cons, List.filter_cons, h1, h2]
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
          omega
        · have h1 : decide (g.op ≠ .not) = true := decide_eq_true h
          have h2 : decide (g.op = .not) = false := decide_eq_false h
          rw [List.filter_cons, List.filter_cons, h1, h2]
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
          omega
    have h1 := hsplit C.gates
    have h2 : (C.gates.filter (fun g => decide (g.op = .not))).length = l := hnotc
    dsimp only [Circuit.size] at *
    omega
  have hnot_take : ((C.gates.take C.size).filter (fun g => decide (g.op = .not))).length = l := by
    dsimp only [Circuit.size]; rw [List.take_length]; exact hnotc
  have peel_ind : ∀ m ≤ C.size, ∀ (wt : ℕ → ℕ) (posDone : ℕ),
      (∀ u, n + 2 + m ≤ u → wt u = 0) →
      (∀ p ∈ Finset.range k, ∃ u ∈ Finset.range (n + 2 + m), 0 < wt u ∧ p ∈ chg u) →
      (let supp := (Finset.range (n + 2 + m)).filter (fun w => 0 < wt w)
       supp.card ≤ t + posDone ∧
       ∀ u ∈ Finset.range (n + 2 + m), wt u ≤ 2 ^ (t + posDone - supp.card)) →
      ∃ (wt0 : ℕ → ℕ) (pos0 : ℕ),
        let supp := (Finset.range (n + 2 + m)).filter (fun w => 0 < wt w)
        let supp0 := (Finset.range (n + 2)).filter (fun w => 0 < wt0 w)
        (∀ u, n + 2 ≤ u → wt0 u = 0) ∧
        pos0 ≤ posDone + ((C.gates.take m).filter (fun g => decide (g.op ≠ .not))).length ∧
        supp0.card ≤ t + pos0 ∧
        t + posDone - supp.card ≤ t + pos0 - supp0.card ∧
        (∀ p ∈ Finset.range k, ∃ u ∈ Finset.range (n + 2), 0 < wt0 u ∧ p ∈ chg u) ∧
        (∑ u ∈ Finset.range (n + 2 + m), wt u * falls u) ≤
          (∑ u ∈ Finset.range (n + 2), wt0 u * falls u) +
            ((C.gates.take m).filter (fun g => decide (g.op = .not))).length * 2 ^ (t + pos0 - supp0.card) := by
    intro m
    induction m with
    | zero =>
      intro _ wt posDone hzero hcov ⟨hsp, hwb⟩
      refine ⟨wt, posDone, by simpa using hzero, by simp, hsp, le_rfl, by simpa using hcov, ?_⟩
      simp
    | succ m ih =>
      intro hm wt posDone hzero hcov ⟨hsp, hwb⟩
      have hmlt : m < C.gates.length := hm
      let g := C.gates[m]
      let idx := n + 2 + m
      let supp := (Finset.range (n + 2 + (m + 1))).filter (fun w => 0 < wt w)
      have hgate_val : ∀ p, wire p idx = g.op.eval (g.inputs.map fun a => wire p a) := by
        intro p
        dsimp only [wire, idx, g]
        rw [← hlenX p, run_gate C.gates _ m hmlt, hlenX p]
        congr 1
        apply List.map_congr_left
        intro a ha
        rw [if_pos (hrb m hmlt a ha)]
      have htake_succ : C.gates.take (m + 1) = C.gates.take m ++ [g] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hmlt]; rfl
      by_cases hwt0 : wt idx = 0
      · have hzero' : ∀ u, n + 2 + m ≤ u → wt u = 0 := by
          intro u hu
          rcases Nat.eq_or_lt_of_le hu with rfl | hgt
          · exact hwt0
          · exact hzero u hgt
        have hsupp_eq : (Finset.range (n + 2 + m)).filter (fun w => 0 < wt w) = supp := by
          ext u; simp only [supp, Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨hu, hpos⟩; exact ⟨by omega, hpos⟩
          · rintro ⟨hu, hpos⟩
            have hne : u ≠ idx := by intro heq; subst heq; omega
            exact ⟨by omega, hpos⟩
        have hcov' : ∀ p ∈ Finset.range k, ∃ u ∈ Finset.range (n + 2 + m), 0 < wt u ∧ p ∈ chg u := by
          intro p hp
          obtain ⟨u, hu, hpu, hpc⟩ := hcov p hp
          rw [Finset.mem_range] at hu
          have hne : u ≠ idx := by intro heq; subst heq; omega
          exact ⟨u, Finset.mem_range.mpr (by omega), hpu, hpc⟩
        have hwb' : ∀ u ∈ Finset.range (n + 2 + m),
            wt u ≤ 2 ^ (t + posDone - ((Finset.range (n + 2 + m)).filter (fun w => 0 < wt w)).card) := by
          intro u hu
          rw [hsupp_eq]
          exact hwb u (Finset.mem_range.mpr (by rw [Finset.mem_range] at hu; omega))
        obtain ⟨wt0, pos0, hz0, hp0, hs0, he0, hc0, hsum0⟩ :=
          ih (by omega) wt posDone hzero' hcov' ⟨by rw [hsupp_eq]; exact hsp, hwb'⟩
        refine ⟨wt0, pos0, hz0, ?_, hs0, ?_, hc0, ?_⟩
        · rw [htake_succ, List.filter_append, List.length_append]; omega
        · change t + posDone - supp.card ≤ _
          rw [← hsupp_eq]; exact he0
        · have hsum_eq : (∑ u ∈ Finset.range (n + 2 + (m + 1)), wt u * falls u) =
              ∑ u ∈ Finset.range (n + 2 + m), wt u * falls u := by
            rw [show n + 2 + (m + 1) = (n + 2 + m) + 1 from rfl, Finset.sum_range_succ, hwt0, Nat.zero_mul,
              Nat.add_zero]
          have htake_not : ((C.gates.take m).filter (fun g => decide (g.op = .not))).length ≤
              ((C.gates.take (m + 1)).filter (fun g => decide (g.op = .not))).length := by
            rw [htake_succ, List.filter_append, List.length_append]; omega
          have := Nat.mul_le_mul_right (2 ^ (t + pos0 - ((Finset.range (n + 2)).filter (fun w => 0 < wt0 w)).card)) htake_not
          omega
      ·
        let c := wt idx
        have hcpos : 0 < c := Nat.pos_of_ne_zero hwt0
        have hidx_mem : idx ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcpos⟩
        let ch : List ℕ :=
          if g.op = .not then (match g.inputs with | [] => [] | a :: _ => [a]) else g.inputs.dedup
        have hch_nd : ch.Nodup := by
          dsimp only [ch]; split_ifs
          · rcases g.inputs with _ | ⟨a, _⟩ <;> simp
          · exact List.nodup_dedup _
        have hch_lt : ∀ a ∈ ch, a < idx := by
          intro a ha
          dsimp only [ch] at ha; split_ifs at ha
          · rcases hin : g.inputs with _ | ⟨x, _⟩
            · rw [hin] at ha; simp at ha
            · rw [hin] at ha; simp at ha; subst a; exact hrb m hmlt x (by rw [hin]; simp)
          · exact hrb m hmlt a (List.mem_dedup.mp ha)
        let wt' : ℕ → ℕ := fun u => (if u = idx then 0 else wt u) + (if u ∈ ch then c else 0)
        have hzero' : ∀ u, n + 2 + m ≤ u → wt' u = 0 := by
          intro u hu
          dsimp only [wt']
          have hnc : u ∉ ch := fun hmem => by have := hch_lt u hmem; omega
          rw [if_neg hnc, Nat.add_zero]
          rcases Nat.eq_or_lt_of_le hu with heq | hgt
          · rw [← heq]; simp [idx]
          · rw [if_neg (by dsimp only [idx]; omega), hzero u hgt]
        have hchg_idx : chg idx ⊆ ch.toFinset.biUnion chg := by
          intro p hp
          obtain ⟨hpk, hne⟩ := Finset.mem_filter.mp hp
          by_contra hno
          apply hne
          have hsame : ∀ a ∈ ch, wire p a = wire (p + 1) a := by
            intro a ha
            by_contra hnea
            exact hno (Finset.mem_biUnion.mpr ⟨a, List.mem_toFinset.mpr ha,
              Finset.mem_filter.mpr ⟨hpk, hnea⟩⟩)
          rw [hgate_val p, hgate_val (p + 1)]
          by_cases hnot : g.op = .not
          · dsimp only [ch] at hsame; rw [if_pos hnot] at hsame
            rw [hnot]
            rcases hin : g.inputs with _ | ⟨a, _⟩
            · simp
            · simp only [List.map_cons, GateOp.eval]
              exact congrArg Bool.not (hsame a (by rw [hin]; simp))
          · congr 1; apply List.map_congr_left; intro a ha
            apply hsame a; dsimp only [ch]; rw [if_neg hnot]; exact List.mem_dedup.mpr ha
        have hcov' : ∀ p ∈ Finset.range k, ∃ u ∈ Finset.range (n + 2 + m), 0 < wt' u ∧ p ∈ chg u := by
          intro p hp
          obtain ⟨u, hu, hpu, hpc⟩ := hcov p hp
          rw [Finset.mem_range] at hu
          by_cases huidx : u = idx
          · subst huidx
            obtain ⟨a, ha, hpa⟩ := Finset.mem_biUnion.mp (hchg_idx hpc)
            have ha_ch := List.mem_toFinset.mp ha
            have halt := hch_lt a ha_ch
            refine ⟨a, Finset.mem_range.mpr halt, ?_, hpa⟩
            dsimp only [wt']; rw [if_pos ha_ch]; omega
          · refine ⟨u, Finset.mem_range.mpr (by omega), ?_, hpc⟩
            dsimp only [wt']; rw [if_neg huidx]; omega
        let supp' := (Finset.range (n + 2 + m)).filter (fun w => 0 < wt' w)
        have hsupp_split : supp' = (supp.erase idx) ∪ ch.toFinset := by
          ext u
          simp only [supp', supp, wt', Finset.mem_union, Finset.mem_erase, Finset.mem_filter,
            Finset.mem_range, List.mem_toFinset]
          constructor
          · rintro ⟨hu, hpos⟩
            by_cases huc : u ∈ ch
            · exact Or.inr huc
            · rw [if_neg huc, Nat.add_zero] at hpos
              have hne : u ≠ idx := by omega
              rw [if_neg hne] at hpos
              exact Or.inl ⟨hne, ⟨by omega, hpos⟩⟩
          · rintro (⟨hne, ⟨hu, hpos⟩⟩ | huc)
            · refine ⟨by omega, ?_⟩; rw [if_neg hne]; omega
            · refine ⟨hch_lt u huc, ?_⟩; rw [if_pos huc]; omega
        let posDone' := if g.op = .not then posDone else posDone + 1
        have hcard_supp : supp'.card ≤ (supp.card - 1) + ch.length ∧
            ((∀ a ∈ ch, wt a = 0) → supp'.card = (supp.card - 1) + ch.length) := by
          constructor
          · rw [hsupp_split]
            calc ((supp.erase idx) ∪ ch.toFinset).card
                ≤ (supp.erase idx).card + ch.toFinset.card := Finset.card_union_le _ _
              _ = (supp.card - 1) + ch.length := by
                  rw [Finset.card_erase_of_mem hidx_mem, List.toFinset_card_of_nodup hch_nd]
          · intro hfresh
            rw [hsupp_split, Finset.card_union_of_disjoint, Finset.card_erase_of_mem hidx_mem,
              List.toFinset_card_of_nodup hch_nd]
            rw [Finset.disjoint_left]
            intro a ha1 ha2
            have ha_ch := List.mem_toFinset.mp ha2
            have hwt_pos := (Finset.mem_filter.mp (Finset.mem_erase.mp ha1).2).2
            have := hfresh a ha_ch
            omega
        have hch_len_bound : (g.op = .not → ch.length ≤ 1) ∧ (g.op ≠ .not → ch.length ≤ 2) := by
          constructor <;> intro hop
          · dsimp only [ch]; rw [if_pos hop]; rcases g.inputs with _ | ⟨_, _⟩ <;> simp
          · dsimp only [ch]; rw [if_neg hop]
            exact le_trans (List.dedup_sublist g.inputs).length_le (hfan g (List.getElem_mem hmlt)).2
        have hsp_supp : supp.card ≤ t + posDone := hsp
        have hsp' : supp'.card ≤ t + posDone' := by
          have h1 := hcard_supp.1
          by_cases hnot : g.op = .not
          · have h2 := hch_len_bound.1 hnot
            dsimp only [posDone']; rw [if_pos hnot]
            have := Finset.card_pos.mpr ⟨idx, hidx_mem⟩; omega
          · have h2 := hch_len_bound.2 hnot
            dsimp only [posDone']; rw [if_neg hnot]
            have := Finset.card_pos.mpr ⟨idx, hidx_mem⟩; omega
        have hE_mono : t + posDone - supp.card ≤ t + posDone' - supp'.card := by
          have h1 := hcard_supp.1
          have hpos_idx : 1 ≤ supp.card := Finset.card_pos.mpr ⟨idx, hidx_mem⟩
          by_cases hnot : g.op = .not
          · have h2 := hch_len_bound.1 hnot
            dsimp only [posDone']; rw [if_pos hnot]; omega
          · have h2 := hch_len_bound.2 hnot
            dsimp only [posDone']; rw [if_neg hnot]; omega
        have hwb' : ∀ u ∈ Finset.range (n + 2 + m), wt' u ≤ 2 ^ (t + posDone' - supp'.card) := by
          intro u hu
          have hu' : u ∈ Finset.range (n + 2 + (m + 1)) := Finset.mem_range.mpr (by rw [Finset.mem_range] at hu; omega)
          have huidx : u ≠ idx := by rw [Finset.mem_range] at hu; omega
          have hw_u := hwb u hu'
          have hw_c : c ≤ 2 ^ (t + posDone - supp.card) := hwb idx (Finset.mem_range.mpr (by omega))
          dsimp only [wt']; rw [if_neg huidx]
          by_cases huc : u ∈ ch
          · rw [if_pos huc]
            by_cases hfresh : wt u = 0
            · rw [hfresh, Nat.zero_add]
              exact hw_c.trans (Nat.pow_le_pow_right (by decide) hE_mono)
            · have hwu_mem : u ∈ supp.erase idx :=
                Finset.mem_erase.mpr ⟨huidx, Finset.mem_filter.mpr ⟨hu', Nat.pos_of_ne_zero hfresh⟩⟩
              have hinter : u ∈ (supp.erase idx) ∩ ch.toFinset :=
                Finset.mem_inter.mpr ⟨hwu_mem, List.mem_toFinset.mpr huc⟩
              have hcard_inter : 1 ≤ ((supp.erase idx) ∩ ch.toFinset).card := Finset.card_pos.mpr ⟨u, hinter⟩
              have hcard_u : supp'.card ≤ (supp.card - 1) + ch.length - 1 := by
                rw [hsupp_split]
                have hcap := Finset.card_union_add_card_inter (supp.erase idx) ch.toFinset
                rw [Finset.card_erase_of_mem hidx_mem, List.toFinset_card_of_nodup hch_nd] at hcap
                omega
              have hpos_idx : 1 ≤ supp.card := Finset.card_pos.mpr ⟨idx, hidx_mem⟩
              have hE_step : t + posDone - supp.card + 1 ≤ t + posDone' - supp'.card := by
                by_cases hnot : g.op = .not
                · have h2 := hch_len_bound.1 hnot
                  dsimp only [posDone']; rw [if_pos hnot]; omega
                · have h2 := hch_len_bound.2 hnot
                  dsimp only [posDone']; rw [if_neg hnot]; omega
              calc wt u + c ≤ 2 ^ (t + posDone - supp.card) + 2 ^ (t + posDone - supp.card) := Nat.add_le_add hw_u hw_c
                _ = 2 ^ (t + posDone - supp.card + 1) := by rw [Nat.pow_succ]; omega
                _ ≤ 2 ^ (t + posDone' - supp'.card) := Nat.pow_le_pow_right (by decide) hE_step
          · rw [if_neg huc, Nat.add_zero]
            exact hw_u.trans (Nat.pow_le_pow_right (by decide) hE_mono)
        obtain ⟨wt0, pos0, hz0, hp0, hs0, he0, hc0, hsum0⟩ :=
          ih (by omega) wt' posDone' hzero' hcov' ⟨hsp', hwb'⟩
        have hsum_push : (∑ u ∈ Finset.range (n + 2 + m), wt u * falls u) + c * (ch.map falls).sum ≤
            ∑ u ∈ Finset.range (n + 2 + m), wt' u * falls u := by
          have hch_sum : (ch.map falls).sum = ∑ u ∈ Finset.range (n + 2 + m), (if u ∈ ch then falls u else 0) := by
            rw [← List.sum_toFinset _ hch_nd]
            have hsub : ch.toFinset ⊆ Finset.range (n + 2 + m) := fun a ha =>
              Finset.mem_range.mpr (hch_lt a (List.mem_toFinset.mp ha))
            rw [← Finset.sum_subset hsub (fun x _ hx => if_neg (fun h => hx (List.mem_toFinset.mpr h)))]
            refine Finset.sum_congr rfl fun u hu => ?_
            rw [if_pos (List.mem_toFinset.mp hu)]
          rw [hch_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro u hu
          have huidx : u ≠ idx := by rw [Finset.mem_range] at hu; omega
          dsimp only [wt']; rw [if_neg huidx]
          split_ifs <;> ring_nf <;> omega
        have hsum_idx : (∑ u ∈ Finset.range (n + 2 + (m + 1)), wt u * falls u) =
            (∑ u ∈ Finset.range (n + 2 + m), wt u * falls u) + c * falls idx := by
          rw [show n + 2 + (m + 1) = (n + 2 + m) + 1 from rfl, Finset.sum_range_succ]
        refine ⟨wt0, pos0, hz0, ?_, hs0, hE_mono.trans he0, hc0, ?_⟩
        · rw [htake_succ, List.filter_append, List.length_append]
          by_cases hnot : g.op = .not
          · dsimp only [posDone'] at hp0; rw [if_pos hnot] at hp0; omega
          · dsimp only [posDone'] at hp0; rw [if_neg hnot] at hp0
            have h1 : ([g].filter (fun g => decide (g.op ≠ .not))).length = 1 := by simp [hnot]
            omega
        · by_cases hnot : g.op = .not
          · have hfall_not : falls idx ≤ (ch.map falls).sum + 1 := by
              dsimp only [ch]; rw [if_pos hnot]
              rcases hin : g.inputs with _ | ⟨a, _⟩
              · have h0 : falls idx = 0 := by
                  dsimp only [falls]; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                  intro p _ ⟨h1, h2⟩
                  rw [hgate_val p] at h1
                  rw [hgate_val (p + 1)] at h2
                  rw [hnot, hin] at h1 h2
                  simp [GateOp.eval] at h1 h2
                omega
              · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
                have hfl : falls idx = ((Finset.range k).filter (fun p => wire p a = false ∧ wire (p + 1) a = true)).card := by
                  dsimp only [falls]; congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_range]
                  constructor <;> rintro ⟨hpk, h1, h2⟩ <;> refine ⟨hpk, ?_, ?_⟩
                  · rw [hgate_val p, hnot, hin] at h1; simp [GateOp.eval] at h1; exact h1
                  · rw [hgate_val (p + 1), hnot, hin] at h2; simp [GateOp.eval] at h2; exact h2
                  · rw [hgate_val p, hnot, hin]; simp [GateOp.eval, h1]
                  · rw [hgate_val (p + 1), hnot, hin]; simp [GateOp.eval, h2]
                rw [hfl]; exact rise_le_fall_add_one (fun p => wire p a) k
            have hc_le : c ≤ 2 ^ (t + pos0 - ((Finset.range (n + 2)).filter (fun w => 0 < wt0 w)).card) := by
              have hc1 := hwb idx (Finset.mem_range.mpr (by omega))
              exact hc1.trans (Nat.pow_le_pow_right (by decide) (hE_mono.trans he0))
            have hnot_add : ((C.gates.take (m + 1)).filter (fun g => decide (g.op = .not))).length =
                ((C.gates.take m).filter (fun g => decide (g.op = .not))).length + 1 := by
              rw [htake_succ, List.filter_append, List.length_append]; simp [hnot]
            rw [hnot_add, Nat.add_mul, Nat.one_mul]
            have hc_mul : c * falls idx ≤ c * (ch.map falls).sum + c := by
              calc c * falls idx ≤ c * ((ch.map falls).sum + 1) := Nat.mul_le_mul_left c hfall_not
                _ = c * (ch.map falls).sum + c := by ring
            omega
          · have hop : g.op = .and ∨ g.op = .or := by
              rcases (hfan g (List.getElem_mem hmlt)).1 with h | h | h
              · exact Or.inl h
              · exact Or.inr h
              · exact absurd h hnot
            have hfall_pos : falls idx ≤ (ch.map falls).sum := by
              dsimp only [ch]; rw [if_neg hnot]
              rcases hop with hand | hor
              · dsimp only [falls]
                have h := gate_fall_and (Finset.range k) g.inputs wire
                refine le_trans ?_ h
                apply Finset.card_le_card; intro p hp
                obtain ⟨hpk, h1, h2⟩ := Finset.mem_filter.mp hp
                rw [hgate_val p, hand] at h1; rw [hgate_val (p + 1), hand] at h2
                exact Finset.mem_filter.mpr ⟨hpk, h1, h2⟩
              · dsimp only [falls]
                have h := gate_fall_or (Finset.range k) g.inputs wire
                refine le_trans ?_ h
                apply Finset.card_le_card; intro p hp
                obtain ⟨hpk, h1, h2⟩ := Finset.mem_filter.mp hp
                rw [hgate_val p, hor] at h1; rw [hgate_val (p + 1), hor] at h2
                exact Finset.mem_filter.mpr ⟨hpk, h1, h2⟩
            have hc_mul := Nat.mul_le_mul_left c hfall_pos
            have hnot_eq : ((C.gates.take (m + 1)).filter (fun g => decide (g.op = .not))).length =
                ((C.gates.take m).filter (fun g => decide (g.op = .not))).length := by
              rw [htake_succ, List.filter_append, List.length_append]; simp [hnot]
            rw [hnot_eq]; omega

  let wtInit : ℕ → ℕ := fun u => (Finset.univ.filter (fun a : Fin t => tap a = u)).card
  have hzero_init : ∀ u, n + 2 + C.size ≤ u → wtInit u = 0 := by
    intro u hu
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a _ heq
    have := htap a; omega
  have hcov_init : ∀ p ∈ Finset.range k, ∃ u ∈ Finset.range (n + 2 + C.size), 0 < wtInit u ∧ p ∈ chg u := by
    intro p hp
    obtain ⟨a, ha⟩ := hchg_cov p (Finset.mem_range.mp hp)
    refine ⟨tap a, Finset.mem_range.mpr (htap a), Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩,
      Finset.mem_filter.mpr ⟨hp, ha⟩⟩
  let suppInit := (Finset.range (n + 2 + C.size)).filter (fun w => 0 < wtInit w)
  have hsum_wtInit : ∑ u ∈ suppInit, wtInit u = t := by
    have hfib : ∑ u ∈ suppInit, (Finset.univ.filter (fun a : Fin t => tap a = u)).card =
        (Finset.univ : Finset (Fin t)).card := by
      rw [← Finset.card_biUnion]
      · congr 1; apply Finset.ext; intro a
        simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, iff_true]
        exact ⟨tap a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (htap a),
          Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩⟩, rfl⟩
      · intro x _ y _ hxy; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro a h1 h2
        simp only [Finset.mem_filter] at h1 h2; exact hxy (h1.2.symm.trans h2.2)
    simpa [wtInit, Fintype.card_fin] using hfib
  have hsp_init : suppInit.card ≤ t + 0 := by
    have hge : ∑ _u ∈ suppInit, 1 ≤ ∑ u ∈ suppInit, wtInit u :=
      Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_one, hsum_wtInit] at hge
    omega
  have hwb_init : ∀ u ∈ Finset.range (n + 2 + C.size), wtInit u ≤ 2 ^ (t + 0 - suppInit.card) := by
    intro u hu
    by_cases hus : u ∈ suppInit
    · have hrest : ∑ v ∈ suppInit.erase u, 1 ≤ ∑ v ∈ suppInit.erase u, wtInit v :=
        Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).2
      have hsplit := Finset.add_sum_erase suppInit wtInit hus
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_one, Finset.card_erase_of_mem hus] at hrest
      rw [hsum_wtInit] at hsplit
      have hpos : 1 ≤ suppInit.card := Finset.card_pos.mpr ⟨u, hus⟩
      have hle : wtInit u ≤ 1 + (t + 0 - suppInit.card) := by omega
      exact hle.trans (nat_le_two_pow _)
    · have h0 : wtInit u = 0 := by
        by_contra hne
        exact hus (Finset.mem_filter.mpr ⟨hu, Nat.pos_of_ne_zero hne⟩)
      rw [h0]; exact Nat.zero_le _
  obtain ⟨wt0, pos0, _, hp0, hs0, _, hc0, hsum0⟩ :=
    peel_ind C.size le_rfl wtInit 0 hzero_init hcov_init ⟨hsp_init, hwb_init⟩
  rw [hpos_count] at hp0
  rw [hnot_take] at hsum0
  simp only [Nat.zero_add] at hp0

  have hchg_base : ∀ u ∈ Finset.range (n + 2), (chg u).card ≤ 1 := by
    intro u hu
    rw [Finset.mem_range] at hu
    rcases Nat.lt_or_ge u n with hun | hun
    · refine Finset.card_le_one.mpr fun p1 hp1 p2 hp2 => ?_
      obtain ⟨hp1k, hne1⟩ := Finset.mem_filter.mp hp1
      obtain ⟨hp2k, hne2⟩ := Finset.mem_filter.mp hp2
      rw [Finset.mem_range] at hp1k hp2k
      have hbit : ∀ p, wire p u = decide (⟨u, hun⟩ ∈ P p) := by
        intro p; dsimp only [wire]
        rw [run_input C.gates _ u (by rw [hlenX p]; omega),
          List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hun]), List.getElem?_ofFn, dif_pos hun]
        rfl
      rw [hbit p1, hbit (p1 + 1)] at hne1
      rw [hbit p2, hbit (p2 + 1)] at hne2
      have h1 : ⟨u, hun⟩ ∉ P p1 ∧ ⟨u, hun⟩ ∈ P (p1 + 1) := by
        by_cases ha : (⟨u, hun⟩ : Fin n) ∈ P p1
        · exact absurd (by simp [ha, hP p1 hp1k ha]) hne1
        · by_cases hb : (⟨u, hun⟩ : Fin n) ∈ P (p1 + 1)
          · exact ⟨ha, hb⟩
          · exact absurd (by simp [ha, hb]) hne1
      have h2 : ⟨u, hun⟩ ∉ P p2 ∧ ⟨u, hun⟩ ∈ P (p2 + 1) := by
        by_cases ha : (⟨u, hun⟩ : Fin n) ∈ P p2
        · exact absurd (by simp [ha, hP p2 hp2k ha]) hne2
        · by_cases hb : (⟨u, hun⟩ : Fin n) ∈ P (p2 + 1)
          · exact ⟨ha, hb⟩
          · exact absurd (by simp [ha, hb]) hne2
      rcases lt_trichotomy p1 p2 with hlt | heq | hgt
      · exact absurd (mono_chain_set n k P hP (p1 + 1) p2 (by omega) (by omega) h1.2) h2.1
      · exact heq
      · exact absurd (mono_chain_set n k P hP (p2 + 1) p1 (by omega) (by omega) h2.2) h1.1
    · have h0 : chg u = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro p _
        dsimp only [wire]
        rw [run_input C.gates _ u (by rw [hlenX p]; exact hu),
          run_input C.gates _ u (by rw [hlenX (p + 1)]; exact hu)]
        have hu' : u = n ∨ u = n + 1 := by omega
        rcases hu' with rfl | rfl <;>
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      simp [h0]
  let supp0 := (Finset.range (n + 2)).filter (fun w => 0 < wt0 w)
  have hk_sub : Finset.range k ⊆ supp0.biUnion chg := fun p hp => by
    obtain ⟨u, hu, hpu, hpc⟩ := hc0 p hp
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hpu⟩, hpc⟩
  have hk_le_s0 : k ≤ supp0.card := by
    calc k = (Finset.range k).card := (Finset.card_range k).symm
      _ ≤ (supp0.biUnion chg).card := Finset.card_le_card hk_sub
      _ ≤ ∑ u ∈ supp0, (chg u).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ supp0, 1 := Finset.sum_le_sum fun u hu => hchg_base u (Finset.mem_filter.mp hu).1
      _ = supp0.card := by simp
  have hfalls_base : ∑ u ∈ Finset.range (n + 2), wt0 u * falls u = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    have h0 : falls u = 0 := by
      dsimp only [falls]; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp ⟨h1, h2⟩
      rw [Finset.mem_range] at hp hu
      rcases Nat.lt_or_ge u n with hun | hun
      · have hbit : ∀ q, wire q u = decide (⟨u, hun⟩ ∈ P q) := by
          intro q; dsimp only [wire]
          rw [run_input C.gates _ u (by rw [hlenX q]; omega),
            List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hun]), List.getElem?_ofFn, dif_pos hun]
          rfl
        rw [hbit p] at h1
        rw [hbit (p + 1)] at h2
        have hmem := hP p hp (of_decide_eq_true h1)
        rw [decide_eq_true hmem] at h2; cases h2
      · dsimp only [wire] at h1 h2
        rw [run_input C.gates _ u (by rw [hlenX p]; exact hu)] at h1
        rw [run_input C.gates _ u (by rw [hlenX (p + 1)]; exact hu)] at h2
        have hu' : u = n ∨ u = n + 1 := by omega
        rcases hu' with rfl | rfl <;>
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_right] at h1 h2
    rw [h0, Nat.mul_zero]
  have htap_sum_le : ∑ a : Fin t, falls (tap a) ≤ ∑ u ∈ Finset.range (n + 2 + C.size), wtInit u * falls u := by
    have h1 : ∑ u ∈ Finset.range (n + 2 + C.size), wtInit u * falls u =
        ∑ u ∈ suppInit, ∑ a ∈ Finset.univ.filter (fun a : Fin t => tap a = u), falls (tap a) := by
      have hflt : ∑ u ∈ Finset.range (n + 2 + C.size), wtInit u * falls u =
          ∑ u ∈ suppInit, wtInit u * falls u := by
        dsimp only [suppInit]; rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : 0 < wtInit u
        · rw [if_pos hu]
        · have h0 : wtInit u = 0 := by omega
          rw [if_neg hu, h0, Nat.zero_mul]
      rw [hflt]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.mp ha).2])]
      simp [wtInit]
    rw [h1, ← Finset.sum_biUnion]
    · apply le_of_eq; apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext a; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, suppInit,
        Finset.mem_range]
      exact ⟨fun _ => ⟨tap a, ⟨htap a, Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩⟩, rfl⟩,
        fun _ => trivial⟩
    · intro x _ y _ hxy; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro a h1 h2
      simp only [Finset.mem_filter] at h1 h2; exact hxy (h1.2.symm.trans h2.2)
  dsimp only [supp0] at hk_le_s0
  have hexp_le : t + pos0 - supp0.card ≤ C.size - l + t - k := by
    dsimp only [supp0]
    omega
  refine ⟨by omega, ?_⟩
  calc ∑ a : Fin t, falls (tap a)
      ≤ ∑ u ∈ Finset.range (n + 2 + C.size), wtInit u * falls u := htap_sum_le
    _ ≤ 0 + l * 2 ^ (t + pos0 - supp0.card) := by rw [← hfalls_base]; exact hsum0
    _ = l * 2 ^ (t + pos0 - supp0.card) := Nat.zero_add _
    _ ≤ l * 2 ^ (C.size - l + t - k) := Nat.mul_le_mul_left l (Nat.pow_le_pow_right (by decide) hexp_le)

private theorem L_lib_1322_core [DecidableEq GateOp] (n m t b : Nat) (ht : 1 ≤ t)
    (x : Fin m → Finset (Fin n)) (block : Fin m → Fin ((t + 1) * 2 ^ b - 1))
    (ok : Fin m → Finset (Fin t) → Prop)
    (hmono : ∀ i j, block i < block j → x i ⊆ x j)
    (hno : ∀ z, ¬ ∃ w : Finset (Fin t), ∀ i, block i = z → ok i w)
    (C : Circuit) (tap : Fin t → Nat)
    (hfan' : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hrb' : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + 2 + j)
    (htap : ∀ a, tap a < n + 2 + C.size) (hnotb : PEqualNP.NotBracket.notCount C ≤ b)
    (lower upper : Fin ((t + 1) * 2 ^ b - 1) → Finset (Fin n))
    (hlow_iff : ∀ z a, a ∈ lower z ↔ ∀ i, block i = z → a ∈ x i)
    (hup_iff : ∀ z a, a ∈ upper z ↔ ∃ i, block i = z ∧ a ∈ x i)
    (hok : ∀ i, ok i (Finset.univ.filter (fun a : Fin t =>
      (run C.gates (List.ofFn (fun u : Fin n => decide (u ∈ x i)) ++ [false, true])).getD (tap a) false = true))) :
    let q := 2 ^ b
    let k := (t + 1) * q - 1
    let wire := fun (X : Finset (Fin n)) (u : Nat) =>
      (run C.gates (List.ofFn (fun a : Fin n => decide (a ∈ X)) ++ [false, true])).getD u false
    let gates := (List.range C.size).filter (fun u => decide ((C.gates.getD u ⟨GateOp.or, []⟩).op = .not))
    let sig := fun X => gates.foldl (fun v u => 2 * v + (if wire X (n + 2 + u) then 1 else 0)) 0
    let word := fun X => Finset.univ.filter (fun a => wire X (tap a) = true)
    let state := fun X => (sig X, word X)
    PEqualNP.NotBracket.notCount C = b ∧
    k ≤ C.size - b + t ∧ t * (q - 1) ≤ b * 2 ^ (C.size - b + t - k) ∧ ∃ order : Nat → Equiv.Perm (Fin t),
      let endpoint := fun p : Nat => (q - 1 - p / (t + 1), Finset.univ.filter
        (fun a : Fin t => (order (p / (t + 1)) a).val < p % (t + 1)))
      ∀ z : Fin k, state (lower z) = endpoint z.val ∧ state (upper z) = endpoint (z.val + 1) ∧
        Finset.image (fun i => state (x i)) (Finset.univ.filter (fun i => block i = z)) =
          {endpoint z.val, endpoint (z.val + 1)} := by
  intro q k wire gates sig word state
  have hq_pos : 0 < q := Nat.two_pow_pos b
  have hk_pos : 0 < k := by
    have : 2 ≤ (t + 1) * q := by nlinarith
    dsimp only [k]; omega
  have hk_eq : k + 1 = (t + 1) * q := by
    have : 2 ≤ (t + 1) * q := by nlinarith
    dsimp only [k]; omega
  have hsig_lt : ∀ Z, sig Z < 2 ^ PEqualNP.NotBracket.notCount C := by
    intro Z; dsimp only [sig, gates, wire]; rw [← notCount_eq_filter_range C]
    exact sigPrefix_bound C _ C.size
  have hsig_lt_q : ∀ Z, sig Z < q := fun Z =>
    (hsig_lt Z).trans_le (Nat.pow_le_pow_right (by decide) hnotb)
  have hmono_sig : ∀ X Y, X ⊆ Y → sig Y ≤ sig X ∧ (sig Y = sig X → word X ⊆ word Y) := by
    intro X Y hXY
    have hm := sigPrefix_mono n C hfan' hrb' X Y hXY C.size le_rfl
    refine ⟨hm.1, fun heq a ha => ?_⟩
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, hm.2 heq (tap a) (htap a) ha.2⟩
  let rank : Finset (Fin n) → ℕ := fun Z => (t + 1) * (q - 1 - sig Z) + (word Z).card
  have hrank_le : ∀ Z, rank Z ≤ k := fun Z => by
    have h1 := hsig_lt_q Z
    have h2 : (word Z).card ≤ t := (Finset.card_le_univ _).trans_eq (Fintype.card_fin t)
    have hmul : (t + 1) * (q - 1 - sig Z) + (t + 1) ≤ (t + 1) * q := by
      have : (q - 1 - sig Z) + 1 ≤ q := by omega
      nlinarith
    dsimp only [rank, k]; omega
  have hrank_mono : ∀ X Y, X ⊆ Y → rank X ≤ rank Y := fun X Y hXY => by
    obtain ⟨hs, hw⟩ := hmono_sig X Y hXY
    have h1 := hsig_lt_q X
    rcases lt_or_eq_of_le hs with hlt | heq
    · have h2 : (word X).card ≤ t := (Finset.card_le_univ _).trans_eq (Fintype.card_fin t)
      have hmul : (t + 1) * (q - 1 - sig X) + (t + 1) ≤ (t + 1) * (q - 1 - sig Y) := by
        have : q - 1 - sig X + 1 ≤ q - 1 - sig Y := by omega
        nlinarith
      dsimp only [rank]; omega
    · have hc : (word X).card ≤ (word Y).card := Finset.card_le_card (hw heq)
      dsimp only [rank]; rw [heq]; omega
  have hrank_eq_state : ∀ X Y, X ⊆ Y → rank X = rank Y → state X = state Y := by
    intro X Y hXY hr
    obtain ⟨hs, hw⟩ := hmono_sig X Y hXY
    have h1 := hsig_lt_q X
    rcases lt_or_eq_of_le hs with hlt | heq
    · have h2 : (word X).card ≤ t := (Finset.card_le_univ _).trans_eq (Fintype.card_fin t)
      have hmul : (t + 1) * (q - 1 - sig X) + (t + 1) ≤ (t + 1) * (q - 1 - sig Y) := by
        have : q - 1 - sig X + 1 ≤ q - 1 - sig Y := by omega
        nlinarith
      dsimp only [rank] at hr; omega
    · have hcard : (word X).card = (word Y).card := by dsimp only [rank] at hr; rw [heq] at hr; omega
      have hweq : word X = word Y := Finset.eq_of_subset_of_card_le (hw heq) (le_of_eq hcard.symm)
      exact Prod.ext heq.symm hweq
  have h_low_mem : ∀ z i, block i = z → lower z ⊆ x i := fun z i hi a ha =>
    (hlow_iff z a).mp ha i hi
  have h_mem_up : ∀ z i, block i = z → x i ⊆ upper z := fun z i hi a ha =>
    (hup_iff z a).mpr ⟨i, hi, ha⟩
  have h_up_low : ∀ z1 z2 : Fin k, z1 < z2 → upper z1 ⊆ lower z2 := fun z1 z2 hz a ha => by
    obtain ⟨i, hi, hai⟩ := (hup_iff z1 a).mp ha
    exact (hlow_iff z2 a).mpr fun j hj => hmono i j (by rw [hi, hj]; exact hz) hai
  have h_block_jump : ∀ z : Fin k, rank (lower z) + 1 ≤ rank (upper z) := by
    intro z
    by_contra hlt
    have hle : rank (upper z) ≤ rank (lower z) := by omega
    have hnonempty : ∃ i, block i = z := by
      by_contra hem
      push_neg at hem
      exact hno z ⟨∅, fun i hi => absurd hi (hem i)⟩
    obtain ⟨i0, hi0⟩ := hnonempty
    have hsub_lu : lower z ⊆ upper z := (h_low_mem z i0 hi0).trans (h_mem_up z i0 hi0)
    have hreq : rank (lower z) = rank (upper z) := le_antisymm (hrank_mono _ _ hsub_lu) hle
    apply hno z
    refine ⟨word (lower z), fun i hi => ?_⟩
    have h1 := hrank_mono _ _ (h_low_mem z i hi)
    have h2 := hrank_mono _ _ (h_mem_up z i hi)
    have hr_eq : rank (lower z) = rank (x i) := by omega
    have hs_eq := hrank_eq_state _ _ (h_low_mem z i hi) hr_eq
    have hw_eq : word (x i) = word (lower z) := (congrArg Prod.snd hs_eq).symm
    rw [← hw_eq]; exact hok i
  have hrank_low_ge : ∀ z (hz : z < k), z ≤ rank (lower ⟨z, hz⟩) := by
    intro z hz
    induction z with
    | zero => exact Nat.zero_le _
    | succ z ih =>
      have hz' : z < k := Nat.lt_of_succ_lt hz
      have h1 := ih hz'
      have h2 := h_block_jump ⟨z, hz'⟩
      have h3 := hrank_mono _ _ (h_up_low ⟨z, hz'⟩ ⟨z + 1, hz⟩ (by simp [Fin.lt_def]))
      omega
  have hrank_up_le : ∀ z (hz : z < k), rank (upper ⟨z, hz⟩) ≤ z + 1 := by
    intro z hz
    have hback : ∀ d, z + d < k → rank (upper ⟨z, hz⟩) + d ≤ k := by
      intro d
      induction d generalizing z with
      | zero => intro _; exact hrank_le _
      | succ d ihd =>
        intro hzd
        have hz1 : z + 1 < k := by omega
        have h1 := hrank_mono _ _ (h_up_low ⟨z, hz⟩ ⟨z + 1, hz1⟩ (by simp [Fin.lt_def]))
        have h2 := h_block_jump ⟨z + 1, hz1⟩
        have h3 := ihd (z + 1) hz1 (by omega)
        omega
    have := hback (k - 1 - z) (by omega)
    omega
  have hrank_low_eq : ∀ z : Fin k, rank (lower z) = z.val := fun ⟨z, hz⟩ => by
    change rank (lower ⟨z, hz⟩) = z
    have h1 := hrank_low_ge z hz; have h2 := h_block_jump ⟨z, hz⟩; have h3 := hrank_up_le z hz; omega
  have hrank_up_eq : ∀ z : Fin k, rank (upper z) = z.val + 1 := fun ⟨z, hz⟩ => by
    change rank (upper ⟨z, hz⟩) = z + 1
    have h1 := hrank_low_ge z hz; have h2 := h_block_jump ⟨z, hz⟩; have h3 := hrank_up_le z hz; omega
  have hnot_eq : PEqualNP.NotBracket.notCount C = b := by
    have h0 : rank (lower ⟨0, hk_pos⟩) = 0 := hrank_low_eq ⟨0, hk_pos⟩
    have hsig0 : sig (lower ⟨0, hk_pos⟩) = q - 1 := by
      dsimp only [rank] at h0
      have : q - 1 - sig (lower ⟨0, hk_pos⟩) = 0 := by
        by_contra hne
        have : 1 ≤ q - 1 - sig (lower ⟨0, hk_pos⟩) := Nat.pos_of_ne_zero hne
        nlinarith
      have hlt := hsig_lt_q (lower ⟨0, hk_pos⟩)
      omega
    have hpow : q - 1 < 2 ^ PEqualNP.NotBracket.notCount C := by rw [← hsig0]; exact hsig_lt _
    by_contra hne
    have hlt : PEqualNP.NotBracket.notCount C < b := lt_of_le_of_ne hnotb hne
    have h2 : 2 ^ PEqualNP.NotBracket.notCount C ≤ 2 ^ (b - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hq2 : 2 * 2 ^ (b - 1) = q := by
      dsimp only [q]
      rw [← Nat.pow_succ']; congr 1; omega
    omega
  let P : ℕ → Finset (Fin n) := fun p =>
    if hp : p = 0 then lower ⟨0, hk_pos⟩
    else if hpk : p - 1 < k then upper ⟨p - 1, hpk⟩
    else upper ⟨k - 1, Nat.sub_lt hk_pos Nat.one_pos⟩
  have hP_rank : ∀ p ≤ k, rank (P p) = p := by
    intro p hp
    dsimp only [P]
    by_cases hp0 : p = 0
    · rw [dif_pos hp0, hp0]; exact hrank_low_eq ⟨0, hk_pos⟩
    · have hpk : p - 1 < k := by omega
      rw [dif_neg hp0, dif_pos hpk]
      have hup := hrank_up_eq ⟨p - 1, hpk⟩
      dsimp only at hup
      omega
  have hP_mono : ∀ p < k, P p ⊆ P (p + 1) := by
    intro p hp
    dsimp only [P]
    by_cases hp0 : p = 0
    · subst hp0; rw [dif_pos rfl, dif_neg (by omega), dif_pos hp]
      by_cases hem : ∃ i, block i = ⟨0, hk_pos⟩
      · obtain ⟨i0, hi0⟩ := hem; exact (h_low_mem _ i0 hi0).trans (h_mem_up _ i0 hi0)
      · push_neg at hem; exact absurd ⟨∅, fun i hi => absurd hi (hem i)⟩ (hno _)
    · have hp1 : p - 1 < k := by omega
      have hp2 : p + 1 - 1 < k := by omega
      rw [dif_neg hp0, dif_pos hp1, dif_neg (by omega), dif_pos hp2]
      have h1 := h_up_low ⟨p - 1, hp1⟩ ⟨p + 1 - 1, hp2⟩ (by simp [Fin.lt_def]; omega)
      have hem : ∃ i, block i = ⟨p + 1 - 1, hp2⟩ := by
        by_contra hem'; push_neg at hem'
        exact hno ⟨p + 1 - 1, hp2⟩ ⟨∅, fun i hi => absurd hi (hem' i)⟩
      obtain ⟨i0, hi0⟩ := hem
      exact h1.trans ((h_low_mem _ i0 hi0).trans (h_mem_up _ i0 hi0))
  have hP_sig_word : ∀ p ≤ k, sig (P p) = q - 1 - p / (t + 1) ∧ (word (P p)).card = p % (t + 1) := by
    intro p hp
    have hr := hP_rank p hp
    dsimp only [rank] at hr
    have hlt_w : (word (P p)).card < t + 1 := by
      have : (word (P p)).card ≤ t := (Finset.card_le_univ _).trans_eq (Fintype.card_fin t)
      omega
    have hdm := Nat.div_add_mod p (t + 1)
    have hmod_lt : p % (t + 1) < t + 1 := Nat.mod_lt p (Nat.zero_lt_succ t)
    have hdiv : q - 1 - sig (P p) = p / (t + 1) := by
      rcases lt_trichotomy (q - 1 - sig (P p)) (p / (t + 1)) with hlt | heq | hgt
      · have hmul : (t + 1) * (q - 1 - sig (P p) + 1) ≤ (t + 1) * (p / (t + 1)) :=
          Nat.mul_le_mul_left (t + 1) hlt
        rw [Nat.mul_add, Nat.mul_one] at hmul
        omega
      · exact heq
      · have hmul : (t + 1) * (p / (t + 1) + 1) ≤ (t + 1) * (q - 1 - sig (P p)) :=
          Nat.mul_le_mul_left (t + 1) hgt
        rw [Nat.mul_add, Nat.mul_one] at hmul
        omega
    have hmod : (word (P p)).card = p % (t + 1) := by
      rw [← hdiv] at hdm; omega
    have hsq := hsig_lt_q (P p)
    have hple : p / (t + 1) ≤ q - 1 := by
      have hmul_le : (t + 1) * (p / (t + 1)) ≤ k := by omega
      have hlt_mul : (t + 1) * (p / (t + 1)) < (t + 1) * q := by omega
      have hlt_q : p / (t + 1) < q := by
        by_contra hge
        push_neg at hge
        have : (t + 1) * q ≤ (t + 1) * (p / (t + 1)) := Nat.mul_le_mul_left (t + 1) hge
        omega
      omega
    exact ⟨by omega, hmod⟩
  have hdiv_step : ∀ L r, r < t + 1 →
      (L * (t + 1) + r) / (t + 1) = L ∧ (L * (t + 1) + r) % (t + 1) = r := by
    intro L r hr
    have hdm := Nat.div_add_mod (L * (t + 1) + r) (t + 1)
    have hm : (L * (t + 1) + r) % (t + 1) < t + 1 := Nat.mod_lt (L * (t + 1) + r) (Nat.zero_lt_succ t)
    have hcomm : (t + 1) * L = L * (t + 1) := Nat.mul_comm (t + 1) L
    have hq : (L * (t + 1) + r) / (t + 1) = L := by
      rcases lt_trichotomy ((L * (t + 1) + r) / (t + 1)) L with hlt | heq | hgt
      · have hmul : (t + 1) * ((L * (t + 1) + r) / (t + 1) + 1) ≤ (t + 1) * L := Nat.mul_le_mul_left (t + 1) hlt
        rw [Nat.mul_add, Nat.mul_one, hcomm] at hmul
        omega
      · exact heq
      · have hmul : (t + 1) * (L + 1) ≤ (t + 1) * ((L * (t + 1) + r) / (t + 1)) := Nat.mul_le_mul_left (t + 1) hgt
        rw [Nat.mul_add, Nat.mul_one, hcomm] at hmul
        omega
    rw [hq, hcomm] at hdm
    exact ⟨hq, by omega⟩
  have hP_state_up_low : ∀ z : Fin k, state (lower z) = state (P z.val) ∧ state (upper z) = state (P (z.val + 1)) := by
    intro ⟨z, hz⟩
    constructor
    · by_cases hz0 : z = 0
      · subst hz0; simp [P]
      · have hzm : z - 1 < k := by omega
        have hsub : upper ⟨z - 1, hzm⟩ ⊆ lower ⟨z, hz⟩ := h_up_low ⟨z - 1, hzm⟩ ⟨z, hz⟩ (by simp [Fin.lt_def]; omega)
        have h1 := hrank_up_eq ⟨z - 1, hzm⟩
        have h2 := hrank_low_eq ⟨z, hz⟩
        dsimp only at h1 h2
        have hreq : rank (upper ⟨z - 1, hzm⟩) = rank (lower ⟨z, hz⟩) := by omega
        have hst := hrank_eq_state _ _ hsub hreq
        dsimp only [P]; rw [dif_neg hz0, dif_pos hzm]; exact hst.symm
    · dsimp only [P]; rw [dif_neg (by omega), Nat.add_sub_cancel, dif_pos hz]
  have hlevel_step : ∀ L < q, ∀ j : Fin t,
      word (P (L * (t + 1) + j.val)) ⊂ word (P (L * (t + 1) + (j.val + 1))) ∧
      (word (P (L * (t + 1) + (j.val + 1))) \ word (P (L * (t + 1) + j.val))).card = 1 := by
    intro L hLq j
    have hp1 : L * (t + 1) + j.val < k := by nlinarith [j.isLt]
    have hp2 : L * (t + 1) + (j.val + 1) ≤ k := by omega
    have hs1 := (hP_sig_word _ (le_of_lt hp1)).1
    have hs2 := (hP_sig_word _ hp2).1
    have hc1 := (hP_sig_word _ (le_of_lt hp1)).2
    have hc2 := (hP_sig_word _ hp2).2
    have hdm1 := hdiv_step L j.val (lt_trans j.isLt (Nat.lt_succ_self t))
    have hdm2 := hdiv_step L (j.val + 1) (Nat.succ_lt_succ j.isLt)
    rw [hdm1.1] at hs1; rw [hdm2.1] at hs2; rw [hdm1.2] at hc1; rw [hdm2.2] at hc2
    have hsub : word (P (L * (t + 1) + j.val)) ⊆ word (P (L * (t + 1) + (j.val + 1))) :=
      (hmono_sig _ _ (hP_mono _ hp1)).2 (hs2.trans hs1.symm)
    have hss : word (P (L * (t + 1) + j.val)) ⊂ word (P (L * (t + 1) + (j.val + 1))) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => by rw [h] at hc1; omega⟩
    have hsdiff := Finset.card_sdiff_of_subset hsub
    exact ⟨hss, by omega⟩
  have hex_elem : ∀ L (hLq : L < q) (j : Fin t), ∃ a : Fin t,
      word (P (L * (t + 1) + (j.val + 1))) \ word (P (L * (t + 1) + j.val)) = {a} :=
    fun L hLq j => Finset.card_eq_one.mp (hlevel_step L hLq j).2
  let pick : ℕ → Fin t → Fin t := fun L j =>
    if hLq : L < q then Classical.choose (hex_elem L hLq j) else j
  have hpick_spec : ∀ L (hLq : L < q) (j : Fin t),
      word (P (L * (t + 1) + (j.val + 1))) \ word (P (L * (t + 1) + j.val)) = {pick L j} := by
    intro L hLq j; dsimp only [pick]; rw [dif_pos hLq]; exact Classical.choose_spec (hex_elem L hLq j)
  have hpick_inj : ∀ L, Function.Injective (pick L) := by
    intro L j1 j2 heq
    by_cases hLq : L < q
    · have hmem : ∀ j : Fin t, pick L j ∈ word (P (L * (t + 1) + (j.val + 1))) ∧
          pick L j ∉ word (P (L * (t + 1) + j.val)) := by
        intro j
        have hm := (hpick_spec L hLq j).symm ▸ Finset.mem_singleton_self (pick L j)
        exact Finset.mem_sdiff.mp hm
      have hsub_chain : ∀ a b : ℕ, a ≤ b → b ≤ t → word (P (L * (t + 1) + a)) ⊆ word (P (L * (t + 1) + b)) := by
        intro a b hab hbt
        induction hab with
        | refl => exact Finset.Subset.rfl
        | @step m hm ih =>
          have h1 := ih (by omega)
          have h2 := (hlevel_step L hLq ⟨m, by omega⟩).1.subset
          exact h1.trans h2
      rcases lt_trichotomy j1.val j2.val with hlt | heqv | hgt
      · have := hsub_chain (j1.val + 1) j2.val hlt (Nat.le_of_lt j2.isLt) (hmem j1).1
        rw [heq] at this; exact absurd this (hmem j2).2
      · exact Fin.ext heqv
      · have := hsub_chain (j2.val + 1) j1.val hgt (Nat.le_of_lt j1.isLt) (hmem j2).1
        rw [← heq] at this; exact absurd this (hmem j1).2
    · dsimp only [pick] at heq; rw [dif_neg hLq, dif_neg hLq] at heq; exact heq
  let order : ℕ → Equiv.Perm (Fin t) := fun L =>
    (Equiv.ofBijective (pick L) ((Fintype.bijective_iff_injective_and_card (pick L)).mpr ⟨hpick_inj L, rfl⟩)).symm
  have hword_P : ∀ L (hLq : L < q) (r : ℕ) (hr : r ≤ t),
      word (P (L * (t + 1) + r)) = Finset.univ.filter (fun a : Fin t => (order L a).val < r) := by
    intro L hLq r hr
    induction r with
    | zero =>
      have h0 : (word (P (L * (t + 1) + 0))).card = 0 := by
        have := (hP_sig_word (L * (t + 1) + 0) (by nlinarith)).2
        rw [(hdiv_step L 0 (Nat.zero_lt_succ t)).2] at this
        exact this
      rw [Finset.card_eq_zero.mp h0]
      ext a; simp
    | succ r ihr =>
      have hsub := (hlevel_step L hLq ⟨r, by omega⟩).1.subset
      have hdiff : word (P (L * (t + 1) + (r + 1))) \ word (P (L * (t + 1) + r)) =
          {pick L ⟨r, by omega⟩} := hpick_spec L hLq ⟨r, by omega⟩
      have heq_ins' : word (P (L * (t + 1) + (r + 1))) =
          insert (pick L ⟨r, by omega⟩) (word (P (L * (t + 1) + r))) := by
        have hsu := Finset.sdiff_union_self_eq_union (s := word (P (L * (t + 1) + (r + 1)))) (t := word (P (L * (t + 1) + r)))
        rw [Finset.union_eq_left.mpr hsub] at hsu
        rw [← hsu, hdiff, Finset.singleton_union]
      rw [heq_ins', ihr (by omega)]
      ext a
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      have hord_pick : order L (pick L ⟨r, by omega⟩) = ⟨r, by omega⟩ :=
        (Equiv.symm_apply_eq _).mpr rfl
      constructor
      · rintro (rfl | hlt)
        · rw [hord_pick]; simp
        · exact Nat.lt_succ_of_lt hlt
      · intro hlt
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hlt' | heq'
        · exact Or.inr hlt'
        · left
          have hinv : order L a = order L (pick L ⟨r, by omega⟩) := by
            rw [hord_pick]; exact Fin.ext heq'
          exact (order L).injective hinv
  have hchg_cov : ∀ p < k, ∃ a : Fin t,
      (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ P p)) ++ [false, true])).getD (tap a) false ≠
      (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ P (p + 1))) ++ [false, true])).getD (tap a) false := by
    intro p hp
    by_contra hnone
    push_neg at hnone
    have hweq : word (P p) = word (P (p + 1)) := by
      ext a
      simp only [word, Finset.mem_filter, Finset.mem_univ, true_and]
      exact eq_iff_iff.mp (congrArg (· = true) (hnone a))
    have hc1 := (hP_sig_word p (le_of_lt hp)).2
    have hc2 := (hP_sig_word (p + 1) hp).2
    rw [hweq] at hc1
    have h1 := Nat.div_add_mod p (t + 1)
    have h2 := Nat.div_add_mod (p + 1) (t + 1)
    have hm1 := Nat.mod_lt p (Nat.zero_lt_succ t)
    have hm2 := Nat.mod_lt (p + 1) (Nat.zero_lt_succ t)
    have hdiv_le : p / (t + 1) ≤ (p + 1) / (t + 1) := Nat.div_le_div_right (Nat.le_succ p)
    rcases lt_or_eq_of_le hdiv_le with hlt | heq
    · have : (t + 1) * (p / (t + 1) + 1) ≤ (t + 1) * ((p + 1) / (t + 1)) := Nat.mul_le_mul_left (t + 1) hlt
      nlinarith
    · nlinarith
  obtain ⟨hk_bound, hfall_bound⟩ := peel_chain n t k b P hP_mono C tap hfan' hrb' htap hnot_eq hchg_cov
  have hfalls_ge : t * (q - 1) ≤ ∑ a : Fin t,
      ((Finset.range k).filter (fun p =>
        (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ P p)) ++ [false, true])).getD (tap a) false = true ∧
        (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ P (p + 1))) ++ [false, true])).getD (tap a) false = false)).card := by
    have hres_mem : ∀ a : Fin t, Finset.image (fun L => L * (t + 1) + t) (Finset.range (q - 1)) ⊆
        (Finset.range k).filter (fun p =>
          (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ P p)) ++ [false, true])).getD (tap a) false = true ∧
          (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ P (p + 1))) ++ [false, true])).getD (tap a) false = false) := by
      intro a p hp
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hp
      rw [Finset.mem_range] at hL
      have hpk : L * (t + 1) + t < k := by
        have hLq2 : L + 2 ≤ q := by omega
        have hmul : (L + 2) * (t + 1) ≤ q * (t + 1) := Nat.mul_le_mul_right (t + 1) hLq2
        dsimp only [k]
        nlinarith
      have hp1 : L * (t + 1) + t + 1 ≤ k := by omega
      have hw1 := hword_P L (by omega) t le_rfl
      have hL1 : L + 1 < q := by omega
      have heq_p1 : L * (t + 1) + t + 1 = (L + 1) * (t + 1) + 0 := by ring
      have hw2 := hword_P (L + 1) hL1 0 (Nat.zero_le t)
      rw [← heq_p1] at hw2
      have ha1 : a ∈ word (P (L * (t + 1) + t)) := by
        rw [hw1, Finset.mem_filter]; exact ⟨Finset.mem_univ _, (order L a).isLt⟩
      have ha2 : a ∉ word (P (L * (t + 1) + t + 1)) := by
        rw [hw2, Finset.mem_filter]; simp
      rw [Finset.mem_filter] at ha1
      have hta1 : wire (P (L * (t + 1) + t)) (tap a) = true := ha1.2
      have hta2 : wire (P (L * (t + 1) + t + 1)) (tap a) = false := by
        by_contra hne
        have ht' : wire (P (L * (t + 1) + t + 1)) (tap a) = true := Bool.eq_true_of_not_eq_false hne
        exact ha2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpk, hta1, hta2⟩
    have hcard_im : ∀ a : Fin t, q - 1 ≤
        ((Finset.range k).filter (fun p =>
          (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ P p)) ++ [false, true])).getD (tap a) false = true ∧
          (run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ P (p + 1))) ++ [false, true])).getD (tap a) false = false)).card := by
      intro a
      have hinj : Function.Injective (fun L : ℕ => L * (t + 1) + t) := fun x y hxy => by
        have hmul : x * (t + 1) = y * (t + 1) := Nat.add_right_cancel hxy
        exact Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_succ t) hmul
      calc q - 1 = (Finset.range (q - 1)).card := (Finset.card_range _).symm
        _ = (Finset.image (fun L => L * (t + 1) + t) (Finset.range (q - 1))).card :=
            (Finset.card_image_of_injective _ hinj).symm
        _ ≤ _ := Finset.card_le_card (hres_mem a)
    calc t * (q - 1) = ∑ _a : Fin t, (q - 1) := by simp [Fintype.card_fin]
      _ ≤ _ := Finset.sum_le_sum fun a _ => hcard_im a
  refine ⟨hnot_eq, hk_bound, hfalls_ge.trans hfall_bound, order, ?_⟩
  intro endpoint z
  have hend : ∀ p ≤ k, state (P p) = endpoint p := fun p hp => by
    have hsw := hP_sig_word p hp
    have hL : p / (t + 1) < q := Nat.div_lt_of_lt_mul (by omega)
    have hr : p % (t + 1) ≤ t := Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.zero_lt_succ t))
    have hpeq : (p / (t + 1)) * (t + 1) + p % (t + 1) = p := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod p (t + 1)
    have hwp := hword_P (p / (t + 1)) hL (p % (t + 1)) hr
    rw [hpeq] at hwp
    dsimp only [state, endpoint]
    exact Prod.ext hsw.1 hwp
  have hlz : state (lower z) = endpoint z.val := (hP_state_up_low z).1.trans (hend z.val (le_of_lt z.isLt))
  have huz : state (upper z) = endpoint (z.val + 1) := (hP_state_up_low z).2.trans (hend (z.val + 1) z.isLt)
  refine ⟨hlz, huz, ?_⟩
  rw [← hlz, ← huz]
  ext s
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have h1 := hrank_mono _ _ (h_low_mem z i hi)
    have h2 := hrank_mono _ _ (h_mem_up z i hi)
    rw [hrank_low_eq z] at h1
    rw [hrank_up_eq z] at h2
    rcases lt_or_eq_of_le h1 with hgt | heq
    · have : rank (x i) = rank (upper z) := by rw [hrank_up_eq z]; omega
      right; exact (hrank_eq_state _ _ (h_mem_up z i hi) this)
    · left; exact (hrank_eq_state _ _ (h_low_mem z i hi) (by rw [hrank_low_eq z]; exact heq)).symm
  · rintro (rfl | rfl)
    · by_contra hnone
      push_neg at hnone
      apply hno z
      refine ⟨word (upper z), fun i hi => ?_⟩
      have h1 := hrank_mono _ _ (h_low_mem z i hi)
      have h2 := hrank_mono _ _ (h_mem_up z i hi)
      rw [hrank_low_eq z] at h1
      rw [hrank_up_eq z] at h2
      have hne_low : state (x i) ≠ state (lower z) := hnone i hi
      have hr_ne : rank (x i) ≠ rank (lower z) := fun h =>
        hne_low (hrank_eq_state _ _ (h_low_mem z i hi) h.symm).symm
      rw [hrank_low_eq z] at hr_ne
      have hr_up : rank (x i) = rank (upper z) := by rw [hrank_up_eq z]; omega
      have hst_up := hrank_eq_state _ _ (h_mem_up z i hi) hr_up
      have hweq : word (x i) = word (upper z) := congrArg Prod.snd hst_up
      rw [← hweq]
      exact hok i
    · by_contra hnone
      push_neg at hnone
      apply hno z
      refine ⟨word (lower z), fun i hi => ?_⟩
      have h1 := hrank_mono _ _ (h_low_mem z i hi)
      have h2 := hrank_mono _ _ (h_mem_up z i hi)
      rw [hrank_low_eq z] at h1
      rw [hrank_up_eq z] at h2
      have hne_up : state (x i) ≠ state (upper z) := hnone i hi
      have hr_ne : rank (x i) ≠ rank (upper z) := fun h =>
        hne_up (hrank_eq_state _ _ (h_mem_up z i hi) h)
      rw [hrank_up_eq z] at hr_ne
      have hr_low : rank (x i) = rank (lower z) := by rw [hrank_low_eq z]; omega
      have hst_low := hrank_eq_state _ _ (h_low_mem z i hi) hr_low.symm
      have hweq : word (lower z) = word (x i) := congrArg Prod.snd hst_low
      rw [hweq]
      exact hok i

end PEqualNP.Outside.L_lib_1322_aux

open PEqualNP.Outside.L_lib_1322_aux PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_lib_1322 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m t b : Nat), 1 ≤ t →
  let q := 2^b
  let k := (t+1)*q-1
  ∀ (x : Fin m → Finset (Fin n)) (block : Fin m → Fin k) (ok : Fin m → Finset (Fin t) → Prop),
    Function.Injective x → (∀ i j, block i < block j → x i ⊆ x j) →
    (∀ z, ¬ ∃ w : Finset (Fin t), ∀ i, block i=z → ok i w) →
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat),
      PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C →
      C.output < n+2+C.size → (∀ a, tap a < n+2+C.size) → PEqualNP.NotBracket.notCount C ≤ b →
      let wire := fun (X : Finset (Fin n)) (u : Nat) =>
        (C.wires (List.ofFn (fun a : Fin n => decide (a ∈ X)) ++ [false,true])).getD u false
      let gates := (List.range C.size).filter (fun u => decide
        ((C.gates.getD u ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not))
      let sig := fun X => gates.foldl (fun v u => 2*v+(if wire X (n+2+u) then 1 else 0)) 0
      let word := fun X => Finset.univ.filter (fun a => wire X (tap a) = true)
      let state := fun X => (sig X,word X)
      let lower := fun z => Finset.univ.filter (fun a => ∀ i, block i=z → a ∈ x i)
      let upper := fun z => Finset.univ.filter (fun a => ∃ i, block i=z ∧ a ∈ x i)
      (∀ i, ok i (word (x i))) →
      PEqualNP.NotBracket.notCount C = b ∧
      k ≤ C.size-b+t ∧ t*(q-1) ≤ b*2^(C.size-b+t-k) ∧ ∃ order : Nat → Equiv.Perm (Fin t),
        let endpoint := fun p : Nat => (q-1-p/(t+1), Finset.univ.filter
          (fun a : Fin t => (order (p/(t+1)) a).val < p % (t+1)))
        ∀ z : Fin k, state (lower z) = endpoint z.val ∧ state (upper z) = endpoint (z.val+1) ∧
          Finset.image (fun i => state (x i)) (Finset.univ.filter (fun i => block i=z)) =
            {endpoint z.val, endpoint (z.val+1)}) := by
  let _ : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro n m t b ht q k x block ok _hx hmono hno C tap hfan hrb _hout htap hnotb
    wire gates sig word state lower upper hok
  have hfan' : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg; obtain ⟨h1, h2⟩ := hfan g hg; exact ⟨by simpa using h1, h2⟩
  have hrb' : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + 2 + j := by
    intro j hj i hi
    exact hrb j hj i (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; rw [List.getD_eq_getElem _ _ hj]; exact hi)
  have hlow_iff : ∀ z a, a ∈ lower z ↔ ∀ i, block i = z → a ∈ x i := by
    intro z a; simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and]
  have hup_iff : ∀ z a, a ∈ upper z ↔ ∃ i, block i = z ∧ a ∈ x i := by
    intro z a; simp only [upper, Finset.mem_filter, Finset.mem_univ, true_and]
  have hwire_bridge : ∀ Z u,
      wire Z u = (PEqualNP.Outside.L_lib_1322_aux.run C.gates
        (List.ofFn (fun a : Fin n => @decide (a ∈ Z) (@Finset.decidableMem (Fin n) (instDecidableEqFin n) a Z)) ++ [false, true])).getD u false := by
    intro Z u
    dsimp only [wire, PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.Outside.L_lib_1322_aux.run]
    congr 3; apply List.ofFn_inj.mpr; funext a; exact congrArg (@decide (a ∈ Z)) (Subsingleton.elim _ _)
  have hok_core : ∀ i, ok i (@Finset.filter (Fin t) (fun a : Fin t =>
      (PEqualNP.Outside.L_lib_1322_aux.run C.gates
        (List.ofFn (fun u : Fin n => @decide (u ∈ x i) (@Finset.decidableMem (Fin n) (instDecidableEqFin n) u (x i))) ++ [false, true])).getD (tap a) false = true)
      (fun a => instDecidableEqBool _ true) Finset.univ) := by
    intro i
    have hi := hok i
    convert hi using 1
    ext a
    simp only [word, Finset.mem_filter, Finset.mem_univ, true_and, hwire_bridge]
  obtain ⟨h1, h2, h3, order, h4⟩ :=
    @PEqualNP.Outside.L_lib_1322_aux.L_lib_1322_core PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
      n m t b ht x block ok hmono hno C tap hfan' hrb' htap hnotb lower upper hlow_iff hup_iff hok_core
  refine ⟨h1, h2, h3, order, ?_⟩
  intro endpoint z
  have h4z := h4 z
  dsimp only at h4z
  let wire_core := fun (X : Finset (Fin n)) (u : Nat) =>
    (PEqualNP.Outside.L_lib_1322_aux.run C.gates
      (List.ofFn (fun a : Fin n => @decide (a ∈ X) (@Finset.decidableMem (Fin n) (instDecidableEqFin n) a X)) ++ [false, true])).getD u false
  have hite : ∀ b : Bool, (if b = true then 1 else 0) = @ite ℕ (b = true) (instDecidableEqBool b true) 1 0 := by
    intro b; cases b <;> simp
  have hsig_bridge : ∀ Z, sig Z =
      ((List.range C.size).filter (fun u =>
        @decide ((C.gates.getD u ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not)
          (@PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq _ _))).foldl
        (fun v u => 2 * v + @ite ℕ (wire_core Z (n + 2 + u) = true) (instDecidableEqBool (wire_core Z (n + 2 + u)) true) 1 0) 0 := by
    intro Z; dsimp only [sig, gates]
    congr 1
    · ext v u; dsimp only [wire_core]; rw [hwire_bridge Z (n + 2 + u), hite]
    · apply List.filter_congr; intro u _
      exact congrArg (@decide ((C.gates.getD u ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not))
        (Subsingleton.elim _ _)
  have hword_bridge : ∀ Z, word Z =
      @Finset.filter (Fin t) (fun a : Fin t => wire_core Z (tap a) = true)
        (fun a => instDecidableEqBool _ true) Finset.univ := by
    intro Z; ext a; simp only [word, wire_core, Finset.mem_filter, Finset.mem_univ, true_and, hwire_bridge]
  have hstate_bridge : ∀ Z, state Z =
      (((List.range C.size).filter (fun u =>
        @decide ((C.gates.getD u ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not)
          (@PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq _ _))).foldl
        (fun v u => 2 * v + @ite ℕ (wire_core Z (n + 2 + u) = true) (instDecidableEqBool (wire_core Z (n + 2 + u)) true) 1 0) 0,
       @Finset.filter (Fin t) (fun a : Fin t => wire_core Z (tap a) = true)
        (fun a => instDecidableEqBool _ true) Finset.univ) :=
    fun Z => Prod.ext (hsig_bridge Z) (hword_bridge Z)
  have hend_bridge : ∀ p, endpoint p =
      (q - 1 - p / (t + 1), @Finset.filter (Fin t)
        (fun a : Fin t => (order (p / (t + 1)) a).val < p % (t + 1))
        (fun a => Nat.decLt _ _) Finset.univ) := by
    intro p; dsimp only [endpoint]; congr 1; ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hstate_bridge (lower z), hstate_bridge (upper z), hend_bridge z.val, hend_bridge (z.val + 1)]
  have hfilt_eq : Finset.univ.filter (fun i : Fin m => block i = z) =
      @Finset.filter (Fin m) (fun i => block i = z) (fun i => instDecidableEqFin k (block i) z) Finset.univ := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have him : Finset.image (fun i => state (x i)) (Finset.univ.filter (fun i => block i = z)) =
      Finset.image (fun i =>
        (((List.range C.size).filter (fun u =>
          @decide ((C.gates.getD u ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not)
            (@PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq _ _))).foldl
          (fun v u => 2 * v + @ite ℕ (wire_core (x i) (n + 2 + u) = true) (instDecidableEqBool (wire_core (x i) (n + 2 + u)) true) 1 0) 0,
         @Finset.filter (Fin t) (fun a : Fin t => wire_core (x i) (tap a) = true)
          (fun a => instDecidableEqBool _ true) Finset.univ))
        (@Finset.filter (Fin m) (fun i => block i = z) (fun i => instDecidableEqFin k (block i) z) Finset.univ) := by
    rw [hfilt_eq]
    congr 1; funext i; exact hstate_bridge (x i)
  rw [him]
  refine ⟨h4z.1, h4z.2.1, ?_⟩
  ext s
  have hs := iff_of_eq (congrArg (s ∈ ·) h4z.2.2)
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hs ⊢
  exact hs
