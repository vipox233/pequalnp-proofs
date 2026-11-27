import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25901_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepW x := rfl

lemma foldl_stepW_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_stepW_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepW_len]

lemma wires_getD_input (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (C.wires x).getD w false = x.getD w false := by
  rw [wires_eq_foldl, foldl_stepW_getD_lt _ _ _ hw]

lemma wires_getD_ge (C : Circuit) (x : List Bool) (w : ℕ) (hw : x.length + C.gates.length ≤ w) :
    (C.wires x).getD w false = false := by
  exact getD_ge_len _ _ (by rw [wires_len]; exact hw)

lemma wires_getD_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (C.gates[j]'hj).op.eval
        ((C.gates[j]'hj).inputs.map fun i =>
          if i < x.length + j then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take j ++ (C.gates[j]'hj) :: C.gates.drop (j + 1) := by
    exact (List.take_append_drop j C.gates).symm.trans (by
      congr 1; exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl stepW x
  have hpre_len : pre.length = x.length + j := by
    rw [foldl_stepW_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have heq : C.wires x = (C.gates.drop (j + 1)).foldl stepW (stepW pre (C.gates[j]'hj)) := by
    rw [wires_eq_foldl]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hpre_get : ∀ i < x.length + j, (C.wires x).getD i false = pre.getD i false := by
    intro i hi
    rw [heq, foldl_stepW_getD_lt _ _ _ (by simp [stepW, hpre_len]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < pre.length by omega)]
  have hnj : (C.wires x).getD (x.length + j) false =
      (C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map fun i => pre.getD i false) := by
    rw [heq, foldl_stepW_getD_lt _ _ _ (by simp [stepW, hpre_len])]
    simp [stepW, List.getD_eq_getElem?_getD, hpre_len]
  rw [hnj]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + j
  · simp only [hi, ↓reduceIte]; exact (hpre_get i hi).symm
  · simp only [hi, ↓reduceIte]; exact getD_ge_len pre i (by omega)

def effList (C : Circuit) (N g : ℕ) : List ℕ :=
  match C.gates[g]? with
  | none => []
  | some gt =>
    match gt.op with
    | GateOp.not =>
      match gt.inputs with
      | w :: _ => if w < N + g then [w] else []
      | [] => []
    | _ => gt.inputs.filter (fun w => decide (w < N + g))

def effSet (C : Circuit) (N g : ℕ) : Finset ℕ :=
  (effList C N g).toFinset

lemma effSet_lt (C : Circuit) (N g w : ℕ) (hw : w ∈ effSet C N g) : w < N + g := by
  unfold effSet effList at hw
  cases h : C.gates[g]? with
  | none => rw [h] at hw; simp at hw
  | some gt =>
    rw [h] at hw
    dsimp only at hw
    cases hop : gt.op <;> rw [hop] at hw <;> dsimp only at hw
    · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw; exact hw.2
    · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw; exact hw.2
    · cases hins : gt.inputs with
      | nil => rw [hins] at hw; simp at hw
      | cons a tl =>
        rw [hins] at hw
        dsimp only at hw
        by_cases hlt : a < N + g
        · rw [if_pos hlt] at hw; simp only [List.mem_toFinset, List.mem_singleton] at hw; omega
        · rw [if_neg hlt] at hw; simp at hw
    · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw; exact hw.2
    · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw; exact hw.2

lemma effSet_card_not (C : Circuit) (N g : ℕ) (hg : g < C.gates.length)
    (hnot : (C.gates[g]'hg).op = GateOp.not) : (effSet C N g).card ≤ 1 := by
  unfold effSet effList
  rw [List.getElem?_eq_getElem hg]
  dsimp only
  rw [hnot]
  dsimp only
  cases (C.gates[g]'hg).inputs with
  | nil => simp
  | cons a tl =>
    dsimp only
    by_cases hlt : a < N + g <;> simp [hlt]

lemma effSet_card_le_two (C : Circuit) (N g : ℕ) (hF : FanInTwo C) (hg : g < C.gates.length) :
    (effSet C N g).card ≤ 2 := by
  have hlen : (C.gates[g]'hg).inputs.length ≤ 2 := (hF _ (List.getElem_mem hg)).2
  unfold effSet effList
  rw [List.getElem?_eq_getElem hg]
  dsimp only
  cases hop : (C.gates[g]'hg).op <;> dsimp only
  · exact le_trans (List.toFinset_card_le _) (le_trans (List.length_filter_le _ _) hlen)
  · exact le_trans (List.toFinset_card_le _) (le_trans (List.length_filter_le _ _) hlen)
  · cases (C.gates[g]'hg).inputs with
    | nil => simp
    | cons a tl =>
      dsimp only
      by_cases hlt : a < N + g <;> simp [hlt]
  · exact le_trans (List.toFinset_card_le _) (le_trans (List.length_filter_le _ _) hlen)
  · exact le_trans (List.toFinset_card_le _) (le_trans (List.length_filter_le _ _) hlen)

lemma mem_effSet_of_and {C : Circuit} {N g a : ℕ} (hg : g < C.gates.length)
    (hop : (C.gates[g]'hg).op = GateOp.and) (ha : a ∈ (C.gates[g]'hg).inputs) (hlt : a < N + g) :
    a ∈ effSet C N g := by
  unfold effSet effList
  rw [List.getElem?_eq_getElem hg]
  dsimp only
  rw [hop]
  dsimp only
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨ha, hlt⟩

lemma mem_effSet_of_or {C : Circuit} {N g a : ℕ} (hg : g < C.gates.length)
    (hop : (C.gates[g]'hg).op = GateOp.or) (ha : a ∈ (C.gates[g]'hg).inputs) (hlt : a < N + g) :
    a ∈ effSet C N g := by
  unfold effSet effList
  rw [List.getElem?_eq_getElem hg]
  dsimp only
  rw [hop]
  dsimp only
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨ha, hlt⟩

lemma mem_effSet_of_not {C : Circuit} {N g a : ℕ} {tl : List ℕ} (hg : g < C.gates.length)
    (hop : (C.gates[g]'hg).op = GateOp.not) (hins : (C.gates[g]'hg).inputs = a :: tl) (hlt : a < N + g) :
    a ∈ effSet C N g := by
  unfold effSet effList
  rw [List.getElem?_eq_getElem hg]
  dsimp only
  rw [hop]
  dsimp only
  rw [hins]
  dsimp only
  rw [if_pos hlt]
  simp

def gateSign (C : Circuit) (g : ℕ) : Bool :=
  match C.gates[g]? with
  | some gt => match gt.op with | GateOp.not => true | _ => false
  | none => false

lemma gateSign_eq_true_iff (C : Circuit) (g : ℕ) (hg : g < C.gates.length) :
    gateSign C g = true ↔ (C.gates[g]'hg).op = GateOp.not := by
  unfold gateSign
  rw [List.getElem?_eq_getElem hg]
  dsimp only
  cases (C.gates[g]'hg).op <;> simp

lemma gateSign_of_and (C : Circuit) (g : ℕ) (hg : g < C.gates.length)
    (hop : (C.gates[g]'hg).op = GateOp.and) : gateSign C g = false := by
  unfold gateSign
  rw [List.getElem?_eq_getElem hg]
  dsimp only
  rw [hop]

lemma gateSign_of_or (C : Circuit) (g : ℕ) (hg : g < C.gates.length)
    (hop : (C.gates[g]'hg).op = GateOp.or) : gateSign C g = false := by
  unfold gateSign
  rw [List.getElem?_eq_getElem hg]
  dsimp only
  rw [hop]

lemma gateSign_of_not (C : Circuit) (g : ℕ) (hg : g < C.gates.length)
    (hop : (C.gates[g]'hg).op = GateOp.not) : gateSign C g = true := by
  unfold gateSign
  rw [List.getElem?_eq_getElem hg]
  dsimp only
  rw [hop]

inductive SReaches (C : Circuit) (N v : ℕ) : Bool → ℕ → Prop
  | refl : SReaches C N v false v
  | step {s : Bool} {u w : ℕ} (hg : w < C.gates.length) (hu : u ∈ effSet C N w)
      (h : SReaches C N v s (N + w)) : SReaches C N v (xor (gateSign C w) s) u

def Reaches (C : Circuit) (N u v : ℕ) : Prop :=
  ∃ s, SReaches C N v s u

inductive ReachesAvoid (C : Circuit) (N u0 v : ℕ) : ℕ → Prop
  | refl (hv : v ≠ u0) : ReachesAvoid C N u0 v v
  | step {u w : ℕ} (hu : u ≠ u0) (hg : w < C.gates.length) (hmem : u ∈ effSet C N w)
      (h : ReachesAvoid C N u0 v (N + w)) : ReachesAvoid C N u0 v u

lemma sreaches_le {C : Circuit} {N v : ℕ} {s : Bool} {u : ℕ} (h : SReaches C N v s u) : u ≤ v := by
  induction h with
  | refl => exact le_rfl
  | step _ hu _ ih =>
    have hlt := effSet_lt C N _ _ hu
    omega

lemma sreaches_refl_eq {C : Circuit} {N v : ℕ} {s : Bool} (h : SReaches C N v s v) :
    s = false := by
  cases h with
  | refl => rfl
  | step _ hu h' =>
    have h1 := effSet_lt C N _ _ hu
    have h2 := sreaches_le h'
    omega

lemma sreaches_trans {C : Circuit} {N u v w : ℕ} {s1 s2 : Bool}
    (h1 : SReaches C N v s1 u) (h2 : SReaches C N w s2 v) :
    SReaches C N w (xor s1 s2) u := by
  induction h1 with
  | refl => simpa using h2
  | step hg hu _ ih =>
    have h3 := SReaches.step hg hu ih
    simpa [Bool.xor_assoc] using h3

lemma reaches_refl (C : Circuit) (N u : ℕ) : Reaches C N u u :=
  ⟨false, SReaches.refl⟩

lemma reaches_le {C : Circuit} {N u v : ℕ} (h : Reaches C N u v) : u ≤ v :=
  let ⟨_, hs⟩ := h; sreaches_le hs

lemma reaches_trans {C : Circuit} {N u v w : ℕ} (h1 : Reaches C N u v) (h2 : Reaches C N v w) :
    Reaches C N u w := by
  obtain ⟨s1, hs1⟩ := h1
  obtain ⟨s2, hs2⟩ := h2
  exact ⟨xor s1 s2, sreaches_trans hs1 hs2⟩

lemma reaches_step {C : Circuit} {N u w v : ℕ} (hg : w < C.gates.length) (hu : u ∈ effSet C N w)
    (h : Reaches C N (N + w) v) : Reaches C N u v := by
  obtain ⟨s, hs⟩ := h
  exact ⟨xor (gateSign C w) s, SReaches.step hg hu hs⟩

lemma reachesAvoid_ne {C : Circuit} {N u0 v u : ℕ} (h : ReachesAvoid C N u0 v u) : u ≠ u0 := by
  cases h with
  | refl hv => exact hv
  | step hu _ _ _ => exact hu

lemma reachesAvoid_reaches {C : Circuit} {N u0 v u : ℕ} (h : ReachesAvoid C N u0 v u) :
    Reaches C N u v := by
  induction h with
  | refl _ => exact reaches_refl C N _
  | step _ hg hmem _ ih => exact reaches_step hg hmem ih

lemma reachesAvoid_trans {C : Circuit} {N u0 u v w : ℕ}
    (h1 : ReachesAvoid C N u0 v u) (h2 : ReachesAvoid C N u0 w v) :
    ReachesAvoid C N u0 w u := by
  induction h1 with
  | refl _ => exact h2
  | step hu hg hmem _ ih => exact ReachesAvoid.step hu hg hmem ih

def evalOv (C : Circuit) (N : ℕ) (x : List Bool) (u0 : ℕ) (b : Bool) (w : ℕ) : Bool :=
  if w = u0 then b
  else if w < N then x.getD w false
  else
    match C.gates[w - N]? with
    | none => false
    | some gt =>
      gt.op.eval (gt.inputs.map fun i => if _ : i < w then evalOv C N x u0 b i else false)
termination_by w

lemma evalOv_eq_wires (C : Circuit) (N : ℕ) (x : List Bool) (hx : x.length = N) (u0 : ℕ) :
    ∀ w : ℕ, evalOv C N x u0 ((C.wires x).getD u0 false) w = (C.wires x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [evalOv]
    by_cases hwu : w = u0
    · simp [hwu]
    · rw [if_neg hwu]
      by_cases hwn : w < N
      · rw [if_pos hwn, wires_getD_input C x w (by omega)]
      · rw [if_neg hwn]
        by_cases hge : C.gates.length ≤ w - N
        · rw [List.getElem?_eq_none hge, wires_getD_ge C x w (by omega)]
        · have hj : w - N < C.gates.length := by omega
          rw [List.getElem?_eq_getElem hj]
          dsimp only
          have hweq : w = x.length + (w - N) := by omega
          have hgate := wires_getD_gate C x (w - N) hj
          rw [← hweq] at hgate
          rw [hgate]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < w
          · simp only [hi, ↓reduceDIte, ↓reduceIte]
            exact ih i hi
          · simp only [hi, ↓reduceDIte, ↓reduceIte]

lemma list_all_mono {l1 l2 : List Bool} (hl : l1.length = l2.length)
    (hle : ∀ i, (hi : i < l1.length) → l1[i] ≤ l2[i]'(by omega)) :
    l1.all id ≤ l2.all id := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => exact le_rfl
    | cons _ _ => simp at hl
  | cons a t1 ih =>
    cases l2 with
    | nil => simp at hl
    | cons b t2 =>
      simp only [List.all_cons, id_eq]
      have h0 : a ≤ b := hle 0 (by simp)
      have ht : t1.all id ≤ t2.all id := ih (by simp at hl; omega) (fun i hi => hle (i + 1) (by simp; omega))
      cases a <;> cases b <;> cases h1 : t1.all id <;> cases h2 : t2.all id <;> simp_all

lemma list_any_mono {l1 l2 : List Bool} (hl : l1.length = l2.length)
    (hle : ∀ i, (hi : i < l1.length) → l1[i] ≤ l2[i]'(by omega)) :
    l1.any id ≤ l2.any id := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => exact le_rfl
    | cons _ _ => simp at hl
  | cons a t1 ih =>
    cases l2 with
    | nil => simp at hl
    | cons b t2 =>
      simp only [List.any_cons, id_eq]
      have h0 : a ≤ b := hle 0 (by simp)
      have ht : t1.any id ≤ t2.any id := ih (by simp at hl; omega) (fun i hi => hle (i + 1) (by simp; omega))
      cases a <;> cases b <;> cases h1 : t1.any id <;> cases h2 : t2.any id <;> simp_all

lemma evalOv_mono (C : Circuit) (N : ℕ) (hF : FanInTwo C) (x : List Bool) (u0 : ℕ) :
    ∀ w : ℕ,
      (¬ SReaches C N w true u0 → evalOv C N x u0 false w ≤ evalOv C N x u0 true w) ∧
      (¬ SReaches C N w false u0 → evalOv C N x u0 true w ≤ evalOv C N x u0 false w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwu : w = u0
    · subst hwu
      constructor
      · intro _; rw [evalOv, if_pos rfl, evalOv, if_pos rfl]; decide
      · intro h; exact absurd SReaches.refl h
    · by_cases hwn : w < N
      · constructor <;> intro _ <;> rw [evalOv, if_neg hwu, if_pos hwn, evalOv, if_neg hwu, if_pos hwn]
      · by_cases hge : C.gates.length ≤ w - N
        · constructor <;> intro _ <;>
            rw [evalOv, if_neg hwu, if_neg hwn, List.getElem?_eq_none hge,
                evalOv, if_neg hwu, if_neg hwn, List.getElem?_eq_none hge]
        · have hj : w - N < C.gates.length := by omega
          have hweq : N + (w - N) = w := by omega
          have hop := (hF _ (List.getElem_mem hj)).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          have hunf : ∀ b : Bool, evalOv C N x u0 b w =
              (C.gates[w - N]'hj).op.eval
                ((C.gates[w - N]'hj).inputs.map fun i => if _ : i < w then evalOv C N x u0 b i else false) := by
            intro b
            rw [evalOv, if_neg hwu, if_neg hwn, List.getElem?_eq_getElem hj]
          rcases hop with hand | hor | hnot
          · have hgs : gateSign C (w - N) = false := gateSign_of_and C (w - N) hj hand
            have hstep : ∀ (s : Bool) (i : ℕ), i ∈ (C.gates[w - N]'hj).inputs → i < w →
                ¬ SReaches C N w s u0 → ¬ SReaches C N i s u0 := by
              intro s i hi hilt hns hs
              have hmem : i ∈ effSet C N (w - N) := mem_effSet_of_and hj hand hi (by omega)
              have h1 : SReaches C N (N + (w - N)) (xor (gateSign C (w - N)) false) i :=
                SReaches.step hj hmem SReaches.refl
              rw [hweq, hgs] at h1
              have hreach : SReaches C N w (xor s (xor false false)) u0 := sreaches_trans hs h1
              simp at hreach
              exact hns hreach
            constructor
            · intro hns
              rw [hunf false, hunf true, hand]
              apply list_all_mono (by simp)
              intro idx hidx
              simp only [List.getElem_map]
              set a := (C.gates[w - N]'hj).inputs[idx]'(by simp at hidx; exact hidx)
              by_cases ha : a < w
              · simp only [ha, ↓reduceDIte]
                exact (ih a ha).1 (hstep true a (List.getElem_mem _) ha hns)
              · simp only [ha, ↓reduceDIte]; exact le_rfl
            · intro hns
              rw [hunf true, hunf false, hand]
              apply list_all_mono (by simp)
              intro idx hidx
              simp only [List.getElem_map]
              set a := (C.gates[w - N]'hj).inputs[idx]'(by simp at hidx; exact hidx)
              by_cases ha : a < w
              · simp only [ha, ↓reduceDIte]
                exact (ih a ha).2 (hstep false a (List.getElem_mem _) ha hns)
              · simp only [ha, ↓reduceDIte]; exact le_rfl
          · have hgs : gateSign C (w - N) = false := gateSign_of_or C (w - N) hj hor
            have hstep : ∀ (s : Bool) (i : ℕ), i ∈ (C.gates[w - N]'hj).inputs → i < w →
                ¬ SReaches C N w s u0 → ¬ SReaches C N i s u0 := by
              intro s i hi hilt hns hs
              have hmem : i ∈ effSet C N (w - N) := mem_effSet_of_or hj hor hi (by omega)
              have h1 : SReaches C N (N + (w - N)) (xor (gateSign C (w - N)) false) i :=
                SReaches.step hj hmem SReaches.refl
              rw [hweq, hgs] at h1
              have hreach : SReaches C N w (xor s (xor false false)) u0 := sreaches_trans hs h1
              simp at hreach
              exact hns hreach
            constructor
            · intro hns
              rw [hunf false, hunf true, hor]
              apply list_any_mono (by simp)
              intro idx hidx
              simp only [List.getElem_map]
              set a := (C.gates[w - N]'hj).inputs[idx]'(by simp at hidx; exact hidx)
              by_cases ha : a < w
              · simp only [ha, ↓reduceDIte]
                exact (ih a ha).1 (hstep true a (List.getElem_mem _) ha hns)
              · simp only [ha, ↓reduceDIte]; exact le_rfl
            · intro hns
              rw [hunf true, hunf false, hor]
              apply list_any_mono (by simp)
              intro idx hidx
              simp only [List.getElem_map]
              set a := (C.gates[w - N]'hj).inputs[idx]'(by simp at hidx; exact hidx)
              by_cases ha : a < w
              · simp only [ha, ↓reduceDIte]
                exact (ih a ha).2 (hstep false a (List.getElem_mem _) ha hns)
              · simp only [ha, ↓reduceDIte]; exact le_rfl
          · have hgs : gateSign C (w - N) = true := gateSign_of_not C (w - N) hj hnot
            cases hins : (C.gates[w - N]'hj).inputs with
            | nil =>
              constructor <;> intro _ <;> (rw [hunf false, hunf true, hnot, hins]; exact le_rfl)
            | cons a tl =>
              by_cases ha : a < w
              · have hmem : a ∈ effSet C N (w - N) := mem_effSet_of_not hj hnot hins (by omega)
                have hstep : ∀ s : Bool, ¬ SReaches C N w s u0 → ¬ SReaches C N a (!s) u0 := by
                  intro s hns hs
                  have h1 : SReaches C N (N + (w - N)) (xor (gateSign C (w - N)) false) a :=
                    SReaches.step hj hmem SReaches.refl
                  rw [hweq, hgs] at h1
                  have hreach : SReaches C N w (xor (!s) (xor true false)) u0 := sreaches_trans hs h1
                  cases s <;> simp at hreach <;> exact hns hreach
                constructor
                · intro hns
                  rw [hunf false, hunf true, hnot, hins]
                  simp only [GateOp.eval, List.map_cons, List.headD_cons, ha, ↓reduceDIte]
                  have hle := (ih a ha).2 (hstep true hns)
                  cases h1 : evalOv C N x u0 false a <;> cases h2 : evalOv C N x u0 true a <;> simp_all
                · intro hns
                  rw [hunf true, hunf false, hnot, hins]
                  simp only [GateOp.eval, List.map_cons, List.headD_cons, ha, ↓reduceDIte]
                  have hle := (ih a ha).1 (hstep false hns)
                  cases h1 : evalOv C N x u0 false a <;> cases h2 : evalOv C N x u0 true a <;> simp_all
              · constructor <;> intro _ <;>
                  (rw [hunf false, hunf true, hnot, hins]; simp [GateOp.eval, ha])

lemma evalOv_indep (C : Circuit) (N : ℕ) (hF : FanInTwo C) (x y : List Bool) (u0 : ℕ) (b : Bool) :
    ∀ w : ℕ, (∀ i < N, ReachesAvoid C N u0 w i → x.getD i false = y.getD i false) →
      evalOv C N x u0 b w = evalOv C N y u0 b w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hagree
    by_cases hwu : w = u0
    · rw [evalOv, if_pos hwu, evalOv, if_pos hwu]
    · by_cases hwn : w < N
      · rw [evalOv, if_neg hwu, if_pos hwn, evalOv, if_neg hwu, if_pos hwn]
        exact hagree w hwn (ReachesAvoid.refl hwu)
      · by_cases hge : C.gates.length ≤ w - N
        · rw [evalOv, if_neg hwu, if_neg hwn, List.getElem?_eq_none hge,
              evalOv, if_neg hwu, if_neg hwn, List.getElem?_eq_none hge]
        · have hj : w - N < C.gates.length := by omega
          have hweq : N + (w - N) = w := by omega
          have hunf : ∀ z : List Bool, evalOv C N z u0 b w =
              (C.gates[w - N]'hj).op.eval
                ((C.gates[w - N]'hj).inputs.map fun i => if _ : i < w then evalOv C N z u0 b i else false) := by
            intro z
            rw [evalOv, if_neg hwu, if_neg hwn, List.getElem?_eq_getElem hj]
          have hchild : ∀ a ∈ effSet C N (w - N), evalOv C N x u0 b a = evalOv C N y u0 b a := by
            intro a ha
            have halt : a < w := by have := effSet_lt C N (w - N) a ha; omega
            by_cases hau : a = u0
            · rw [evalOv, if_pos hau, evalOv, if_pos hau]
            · apply ih a halt
              intro i hi hia
              apply hagree i hi
              have hstep : ReachesAvoid C N u0 (N + (w - N)) a :=
                ReachesAvoid.step hau hj ha (ReachesAvoid.refl (by omega))
              rw [hweq] at hstep
              exact reachesAvoid_trans hia hstep
          have hop := (hF _ (List.getElem_mem hj)).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hand | hor | hnot
          · rw [hunf x, hunf y, hand]
            congr 1
            apply List.map_congr_left
            intro a ha
            by_cases halt : a < w
            · simp only [halt, ↓reduceDIte]
              exact hchild a (mem_effSet_of_and hj hand ha (by omega))
            · simp only [halt, ↓reduceDIte]
          · rw [hunf x, hunf y, hor]
            congr 1
            apply List.map_congr_left
            intro a ha
            by_cases halt : a < w
            · simp only [halt, ↓reduceDIte]
              exact hchild a (mem_effSet_of_or hj hor ha (by omega))
            · simp only [halt, ↓reduceDIte]
          · rw [hunf x, hunf y, hnot]
            cases hins : (C.gates[w - N]'hj).inputs with
            | nil => rfl
            | cons a tl =>
              simp only [GateOp.eval, List.map_cons, List.headD_cons]
              by_cases halt : a < w
              · simp only [halt, ↓reduceDIte]
                congr 1
                exact hchild a (mem_effSet_of_not hj hnot hins (by omega))
              · simp only [halt, ↓reduceDIte]

lemma wires_indep (C : Circuit) (N : ℕ) (hF : FanInTwo C) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (w : ℕ)
    (hagree : ∀ i < N, Reaches C N i w → x.getD i false = y.getD i false) :
    (C.wires x).getD w false = (C.wires y).getD w false := by
  set u0 := N + C.gates.length + w + 1
  have h1 : (C.wires x).getD u0 false = false := wires_getD_ge C x u0 (by omega)
  have h2 : (C.wires y).getD u0 false = false := wires_getD_ge C y u0 (by omega)
  rw [← evalOv_eq_wires C N x hx u0 w, h1, ← evalOv_eq_wires C N y hy u0 w, h2]
  apply evalOv_indep C N hF x y u0 false w
  intro i hi hra
  exact hagree i hi (reachesAvoid_reaches hra)

lemma wires_mono_cone (C : Circuit) (N : ℕ) (hF : FanInTwo C) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) :
    ∀ w : ℕ,
      (∀ (g : ℕ) (hg : g < C.gates.length), Reaches C N (N + g) w → (C.gates[g]'hg).op ≠ GateOp.not) →
      (∀ i < N, Reaches C N i w → x.getD i false ≤ y.getD i false) →
      (C.wires x).getD w false ≤ (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hnoNot hle
    by_cases hwn : w < N
    · rw [wires_getD_input C x w (by omega), wires_getD_input C y w (by omega)]
      exact hle w hwn (reaches_refl C N w)
    · by_cases hge : C.gates.length ≤ w - N
      · rw [wires_getD_ge C x w (by omega), wires_getD_ge C y w (by omega)]
      · have hj : w - N < C.gates.length := by omega
        have hweq : N + (w - N) = w := by omega
        have hwx := wires_getD_gate C x (w - N) hj
        have hwy := wires_getD_gate C y (w - N) hj
        rw [hx, hweq] at hwx
        rw [hy, hweq] at hwy
        rw [hwx, hwy]
        have hop := (hF _ (List.getElem_mem hj)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        have hne_not : (C.gates[w - N]'hj).op ≠ GateOp.not :=
          hnoNot (w - N) hj (by rw [hweq]; exact reaches_refl C N w)
        rcases hop with hand | hor | hnot
        · rw [hand]
          apply list_all_mono (by simp)
          intro idx hidx
          simp only [List.getElem_map]
          set a := (C.gates[w - N]'hj).inputs[idx]'(by simp at hidx; exact hidx)
          by_cases ha : a < w
          · simp only [ha, ↓reduceIte]
            have hmem : a ∈ effSet C N (w - N) := mem_effSet_of_and hj hand (List.getElem_mem _) (by omega)
            have hstep : Reaches C N a w := by
              rw [← hweq]; exact reaches_step hj hmem (reaches_refl C N _)
            exact ih a ha
              (fun g hg hr => hnoNot g hg (reaches_trans hr hstep))
              (fun i hi hr => hle i hi (reaches_trans hr hstep))
          · simp only [ha, ↓reduceIte]; exact le_rfl
        · rw [hor]
          apply list_any_mono (by simp)
          intro idx hidx
          simp only [List.getElem_map]
          set a := (C.gates[w - N]'hj).inputs[idx]'(by simp at hidx; exact hidx)
          by_cases ha : a < w
          · simp only [ha, ↓reduceIte]
            have hmem : a ∈ effSet C N (w - N) := mem_effSet_of_or hj hor (List.getElem_mem _) (by omega)
            have hstep : Reaches C N a w := by
              rw [← hweq]; exact reaches_step hj hmem (reaches_refl C N _)
            exact ih a ha
              (fun g hg hr => hnoNot g hg (reaches_trans hr hstep))
              (fun i hi hr => hle i hi (reaches_trans hr hstep))
          · simp only [ha, ↓reduceIte]; exact le_rfl
        · exact absurd hnot hne_not

def bitVec {n m : ℕ} (L : Finset (Fin n)) (Q : Finset (Fin m)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ L)) ++ List.ofFn (fun j : Fin m => decide (j ∈ Q))

lemma bitVec_len {n m : ℕ} (L : Finset (Fin n)) (Q : Finset (Fin m)) :
    (bitVec L Q).length = n + m := by
  simp [bitVec]

lemma bitVec_getD_left {n m : ℕ} (L : Finset (Fin n)) (Q : Finset (Fin m)) (i : Fin n) :
    (bitVec L Q).getD i.val false = decide (i ∈ L) := by
  unfold bitVec
  have hi : i.val < (List.ofFn fun u : Fin n => decide (u ∈ L)).length := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, List.getElem?_eq_getElem hi,
      Option.getD_some, List.getElem_ofFn]

lemma bitVec_getD_right {n m : ℕ} (L : Finset (Fin n)) (Q : Finset (Fin m)) (j : Fin m) :
    (bitVec L Q).getD (n + j.val) false = decide (j ∈ Q) := by
  unfold bitVec
  have hlen : (List.ofFn fun u : Fin n => decide (u ∈ L)).length = n := List.length_ofFn
  have hj : j.val < (List.ofFn fun v : Fin m => decide (v ∈ Q)).length := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some, List.getElem_ofFn]

lemma oneEach_eq_bitVec {n m : ℕ} (i : Fin n) (j : Fin m) :
    oneEach i j = bitVec {i} {j} := by
  unfold oneEach bitVec
  congr 1 <;> (apply congrArg List.ofFn; funext k; simp)

lemma oneEach_len {n m : ℕ} (i : Fin n) (j : Fin m) : (oneEach i j).length = n + m := by
  rw [oneEach_eq_bitVec, bitVec_len]

lemma exists_two_ne_nat {k : ℕ} (hk : 3 ≤ k) (t : ℕ) :
    ∃ a b : Fin k, a ≠ b ∧ a.val ≠ t ∧ b.val ≠ t := by
  by_cases h0 : t = 0
  · refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, Fin.ne_of_val_ne (by simp), by simp [h0], by simp [h0]⟩
  · by_cases h1 : t = 1
    · refine ⟨⟨0, by omega⟩, ⟨2, by omega⟩, Fin.ne_of_val_ne (by simp), by simp [h1], by simp [h1]⟩
    · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne (by simp), by simp; omega, by simp; omega⟩

lemma output_bounds {n m : ℕ} (A : Fin n → Fin m → Bool) (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hRowInj : Function.Injective A) (hColInj : Function.Injective (fun j i => A i j))
    (C : Circuit) (hRep : Represents A C) :
    n + m ≤ C.output ∧ C.output < n + m + C.gates.length := by
  have hlt : C.output < n + m + C.gates.length := by
    by_contra hge
    push Not at hge
    have h01 : A ⟨0, by omega⟩ = A ⟨1, by omega⟩ := by
      funext j
      rw [← hRep ⟨0, by omega⟩ j, ← hRep ⟨1, by omega⟩ j]
      unfold Circuit.eval
      rw [wires_getD_ge C _ _ (by rw [oneEach_len]; omega),
          wires_getD_ge C _ _ (by rw [oneEach_len]; omega)]
    have := hRowInj h01
    have hval := congrArg Fin.val this
    simp at hval
  have hge : n + m ≤ C.output := by
    by_contra hlt'
    push Not at hlt'
    by_cases h1 : C.output < n
    · obtain ⟨a, b, hab, ha, hb⟩ := exists_two_ne_nat hn C.output
      have heq : A a = A b := by
        funext j
        rw [← hRep a j, ← hRep b j]
        unfold Circuit.eval
        rw [oneEach_eq_bitVec, oneEach_eq_bitVec,
            wires_getD_input C _ _ (by rw [bitVec_len]; omega),
            wires_getD_input C _ _ (by rw [bitVec_len]; omega)]
        have ha' := bitVec_getD_left ({a} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨C.output, h1⟩
        have hb' := bitVec_getD_left ({b} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨C.output, h1⟩
        rw [ha', hb']
        have hna : (⟨C.output, h1⟩ : Fin n) ≠ a := fun e => ha (congrArg Fin.val e).symm
        have hnb : (⟨C.output, h1⟩ : Fin n) ≠ b := fun e => hb (congrArg Fin.val e).symm
        simp [hna, hnb]
      exact hab (hRowInj heq)
    · have h2 : C.output - n < m := by omega
      obtain ⟨a, b, hab, ha, hb⟩ := exists_two_ne_nat hm (C.output - n)
      have heq : (fun i => A i a) = (fun i => A i b) := by
        funext i
        rw [← hRep i a, ← hRep i b]
        unfold Circuit.eval
        rw [oneEach_eq_bitVec, oneEach_eq_bitVec,
            wires_getD_input C _ _ (by rw [bitVec_len]; omega),
            wires_getD_input C _ _ (by rw [bitVec_len]; omega)]
        have hco : C.output = n + (⟨C.output - n, h2⟩ : Fin m).val := by simp; omega
        rw [hco, bitVec_getD_right, bitVec_getD_right]
        have hna : (⟨C.output - n, h2⟩ : Fin m) ≠ a := fun e => ha (congrArg Fin.val e).symm
        have hnb : (⟨C.output - n, h2⟩ : Fin m) ≠ b := fun e => hb (congrArg Fin.val e).symm
        simp [hna, hnb]
      exact hab (hColInj heq)
  exact ⟨hge, hlt⟩

lemma sum_sub_one_add_card {α : Type*} (s : Finset α) (f : α → ℕ) (hpos : ∀ a ∈ s, 1 ≤ f a) :
    (∑ a ∈ s, (f a - 1)) + s.card = ∑ a ∈ s, f a := by
  have h : ∑ a ∈ s, ((f a - 1) + 1) = ∑ a ∈ s, f a :=
    Finset.sum_congr rfl fun a ha => Nat.sub_add_cancel (hpos a ha)
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at h
  exact h

lemma unique_of_sum_eq_one {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (hsum : ∑ a ∈ s, f a = 1) :
    ∃ x ∈ s, f x = 1 ∧ ∀ y ∈ s, y ≠ x → f y = 0 := by
  have hex : ∃ x ∈ s, f x ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : ∑ a ∈ s, f a = 0 := Finset.sum_eq_zero hall
    omega
  obtain ⟨x, hx, hfx⟩ := hex
  have hsplit := Finset.add_sum_erase s f hx
  have hfx1 : f x = 1 := by omega
  have hrest0 : ∑ a ∈ s.erase x, f a = 0 := by omega
  refine ⟨x, hx, hfx1, fun y hy hne => ?_⟩
  have hmem : y ∈ s.erase x := Finset.mem_erase.mpr ⟨hne, hy⟩
  exact (Finset.sum_eq_zero_iff.mp hrest0) y hmem

lemma card_eq_sub_one_exists_missing {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (hcard : s.card + 1 = Fintype.card α) :
    ∃ x : α, x ∉ s ∧ ∀ y : α, y ∉ s → y = x := by
  have hcompl : sᶜ.card = 1 := by
    have := Finset.card_compl s
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcompl
  refine ⟨x, ?_, ?_⟩
  · have : x ∈ sᶜ := by rw [hx]; simp
    exact Finset.mem_compl.mp this
  · intro y hy
    have : y ∈ sᶜ := Finset.mem_compl.mpr hy
    rw [hx, Finset.mem_singleton] at this
    exact this

lemma st_card_ge_two {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hRowIncomp : ∀ i : Fin n, ∃ k : Fin n,
      ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (hColIncomp : ∀ j : Fin m, ∃ l : Fin m,
      ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (r : Fin n) (c : Fin m) (S : Finset (Fin n)) (T : Finset (Fin m))
    (W : Finset (Fin n) → Finset (Fin m) → Bool)
    (K : Finset (Fin n) → Finset (Fin m) → Bool → Bool)
    (hr_not_S : r ∉ S) (hc_not_T : c ∉ T)
    (hS_comp : ∀ i ∈ S, (∀ j, A r j = true → A i j = true) ∨ (∀ j, A i j = true → A r j = true))
    (hT_comp : ∀ j ∈ T, (∀ i, A i c = true → A i j = true) ∨ (∀ i, A i j = true → A i c = true))
    (hW_mono : ∀ l l' q q', l ⊆ l' → q ⊆ q' → W l q = true → W l' q' = true)
    (hfactor : ∀ i j, A i j = K ({i} ∩ S) ({j} ∩ T) (W (({i} \ S).erase r) (({j} \ T).erase c))) :
    2 ≤ S.card + T.card := by
  by_contra hlt
  have hzero : S = ∅ ∨ T = ∅ := by
    have : S.card = 0 ∨ T.card = 0 := by omega
    rcases this with h | h
    · exact Or.inl (Finset.card_eq_zero.mp h)
    · exact Or.inr (Finset.card_eq_zero.mp h)
  rcases hzero with hS0 | hT0
  · obtain ⟨l, hl⟩ := hColIncomp c
    have hl_notT : l ∉ T := fun hmem => hl (hT_comp l hmem)
    have hl_ne_c : l ≠ c := fun e => hl (Or.inl fun _ h => by rwa [e])
    have hiS : ∀ i : Fin n, ({i} : Finset (Fin n)) ∩ S = ∅ := fun i => by rw [hS0, Finset.inter_empty]
    have hcT : ({c} : Finset (Fin m)) ∩ T = ∅ := by
      ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl; exact hc_not_T
    have hcer : (({c} : Finset (Fin m)) \ T).erase c = ∅ := by
      ext x; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨h1, h2, _⟩; exact h1 h2
    have hlT : ({l} : Finset (Fin m)) ∩ T = ∅ := by
      ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl; exact hl_notT
    have hler : (({l} : Finset (Fin m)) \ T).erase c = {l} := by
      ext x; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨h ▸ hl_ne_c, h, h ▸ hl_notT⟩⟩
    have hAc : ∀ i : Fin n, A i c = K ∅ ∅ (W (({i} \ S).erase r) ∅) := fun i => by
      have := hfactor i c; rw [hiS i, hcT, hcer] at this; exact this
    have hAl : ∀ i : Fin n, A i l = K ∅ ∅ (W (({i} \ S).erase r) {l}) := fun i => by
      have := hfactor i l; rw [hiS i, hlT, hler] at this; exact this
    cases h0 : K ∅ ∅ false <;> cases h1 : K ∅ ∅ true
    · apply hl; left; intro i hic
      rw [hAc i] at hic
      cases hw1 : W (({i} \ S).erase r) ∅ <;> rw [hw1] at hic
      · rw [h0] at hic; cases hic
      · rw [h1] at hic; cases hic
    · apply hl; left; intro i hic
      rw [hAc i] at hic; rw [hAl i]
      cases hw1 : W (({i} \ S).erase r) ∅ with
      | false => rw [hw1, h0] at hic; cases hic
      | true =>
        have hw2 : W (({i} \ S).erase r) {l} = true :=
          hW_mono _ _ _ _ Finset.Subset.rfl (Finset.empty_subset _) hw1
        rw [hw2, h1]
    · apply hl; right; intro i hil
      rw [hAl i] at hil; rw [hAc i]
      cases hw1 : W (({i} \ S).erase r) ∅ with
      | false => rw [h0]
      | true =>
        have hw2 : W (({i} \ S).erase r) {l} = true :=
          hW_mono _ _ _ _ Finset.Subset.rfl (Finset.empty_subset _) hw1
        rw [hw2, h1] at hil; cases hil
    · apply hl; left; intro i _
      rw [hAl i]
      cases W (({i} \ S).erase r) {l} <;> [exact h0; exact h1]
  · obtain ⟨k, hk⟩ := hRowIncomp r
    have hk_notS : k ∉ S := fun hmem => hk (hS_comp k hmem)
    have hk_ne_r : k ≠ r := fun e => hk (Or.inl fun _ h => by rwa [e])
    have hjT : ∀ j : Fin m, ({j} : Finset (Fin m)) ∩ T = ∅ := fun j => by rw [hT0, Finset.inter_empty]
    have hrS : ({r} : Finset (Fin n)) ∩ S = ∅ := by
      ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl; exact hr_not_S
    have hrer : (({r} : Finset (Fin n)) \ S).erase r = ∅ := by
      ext x; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨h1, h2, _⟩; exact h1 h2
    have hkS : ({k} : Finset (Fin n)) ∩ S = ∅ := by
      ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl; exact hk_notS
    have hker : (({k} : Finset (Fin n)) \ S).erase r = {k} := by
      ext x; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨h ▸ hk_ne_r, h, h ▸ hk_notS⟩⟩
    have hAr : ∀ j : Fin m, A r j = K ∅ ∅ (W ∅ (({j} \ T).erase c)) := fun j => by
      have := hfactor r j; rw [hrS, hjT j, hrer] at this; exact this
    have hAk : ∀ j : Fin m, A k j = K ∅ ∅ (W {k} (({j} \ T).erase c)) := fun j => by
      have := hfactor k j; rw [hkS, hjT j, hker] at this; exact this
    cases h0 : K ∅ ∅ false <;> cases h1 : K ∅ ∅ true
    · apply hk; left; intro j hrj
      rw [hAr j] at hrj
      cases hw1 : W ∅ (({j} \ T).erase c) <;> rw [hw1] at hrj
      · rw [h0] at hrj; cases hrj
      · rw [h1] at hrj; cases hrj
    · apply hk; left; intro j hrj
      rw [hAr j] at hrj; rw [hAk j]
      cases hw1 : W ∅ (({j} \ T).erase c) with
      | false => rw [hw1, h0] at hrj; cases hrj
      | true =>
        have hw2 : W {k} (({j} \ T).erase c) = true :=
          hW_mono _ _ _ _ (Finset.empty_subset _) Finset.Subset.rfl hw1
        rw [hw2, h1]
    · apply hk; right; intro j hkj
      rw [hAk j] at hkj; rw [hAr j]
      cases hw1 : W ∅ (({j} \ T).erase c) with
      | false => rw [h0]
      | true =>
        have hw2 : W {k} (({j} \ T).erase c) = true :=
          hW_mono _ _ _ _ (Finset.empty_subset _) Finset.Subset.rfl hw1
        rw [hw2, h1] at hkj; cases hkj
    · apply hk; left; intro j _
      rw [hAk j]
      cases W {k} (({j} \ T).erase c) <;> [exact h0; exact h1]

lemma binate_left_of_omitted {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hRowIncomp : ∀ i : Fin n, ∃ k : Fin n,
      ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (C : Circuit) (hF : FanInTwo C) (hRep : Represents A C)
    (o : ℕ) (hout_eq : C.output = n + m + o)
    (r0 : Fin n) (hnr0 : ¬ Reaches C (n + m) r0.val (n + m + o)) :
    ∃ k : Fin n, SReaches C (n + m) (n + m + o) false k.val ∧
      SReaches C (n + m) (n + m + o) true k.val := by
  set N := n + m
  obtain ⟨k, hk⟩ := hRowIncomp r0
  have heval_r : ∀ j : Fin m, A r0 j = (C.wires (bitVec (∅ : Finset (Fin n)) {j})).getD (N + o) false := by
    intro j
    rw [← hRep r0 j, Circuit.eval, hout_eq, oneEach_eq_bitVec]
    apply wires_indep C N hF _ _ (bitVec_len _ _) (bitVec_len _ _) (N + o)
    intro w hw hwr
    by_cases h1 : w < n
    · have hne : (⟨w, h1⟩ : Fin n) ≠ r0 := fun e => hnr0 (by simpa [← e] using hwr)
      rw [bitVec_getD_left ({r0} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩,
          bitVec_getD_left (∅ : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩]
      simp [hne]
    · have h2 : w - n < m := by omega
      have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
      rw [hwe, bitVec_getD_right, bitVec_getD_right]
  have hflip : ∀ j : Fin m, evalOv C N (bitVec (∅ : Finset (Fin n)) {j}) k.val true (N + o) = A k j := by
    intro j
    rw [← hRep k j, Circuit.eval, hout_eq, oneEach_eq_bitVec]
    have hkval : (C.wires (bitVec {k} {j})).getD k.val false = true := by
      rw [wires_getD_input C _ _ (by rw [bitVec_len]; omega), bitVec_getD_left]; simp
    rw [← evalOv_eq_wires C N (bitVec {k} {j}) (bitVec_len _ _) k.val (N + o), hkval]
    apply evalOv_indep C N hF _ _ k.val true (N + o)
    intro w hw hwa
    have hne : w ≠ k.val := reachesAvoid_ne hwa
    by_cases h1 : w < n
    · have hne' : (⟨w, h1⟩ : Fin n) ≠ k := fun e => hne (congrArg Fin.val e)
      rw [bitVec_getD_left (∅ : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩,
          bitVec_getD_left ({k} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩]
      simp [hne']
    · have h2 : w - n < m := by omega
      have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
      rw [hwe, bitVec_getD_right, bitVec_getD_right]
  have hzero : ∀ j : Fin m, evalOv C N (bitVec (∅ : Finset (Fin n)) {j}) k.val false (N + o) = A r0 j := by
    intro j
    have hkval : (C.wires (bitVec (∅ : Finset (Fin n)) {j})).getD k.val false = false := by
      rw [wires_getD_input C _ _ (by rw [bitVec_len]; omega), bitVec_getD_left]; simp
    have h0 := evalOv_eq_wires C N (bitVec (∅ : Finset (Fin n)) {j}) (bitVec_len _ _) k.val (N + o)
    rw [hkval] at h0
    rw [h0, ← heval_r j]
  refine ⟨k, ?_, ?_⟩
  · by_contra hnf
    apply hk; right; intro j hkj
    have hle := (evalOv_mono C N hF (bitVec (∅ : Finset (Fin n)) {j}) k.val (N + o)).2 hnf
    rw [hflip j, hzero j, hkj] at hle
    exact Bool.eq_true_of_true_le hle
  · by_contra hnt
    apply hk; left; intro j hrj
    have hle := (evalOv_mono C N hF (bitVec (∅ : Finset (Fin n)) {j}) k.val (N + o)).1 hnt
    rw [hflip j, hzero j, hrj] at hle
    exact Bool.eq_true_of_true_le hle

lemma binate_right_of_omitted {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hColIncomp : ∀ j : Fin m, ∃ l : Fin m,
      ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (C : Circuit) (hF : FanInTwo C) (hRep : Represents A C)
    (o : ℕ) (hout_eq : C.output = n + m + o)
    (c0 : Fin m) (hnc0 : ¬ Reaches C (n + m) (n + c0.val) (n + m + o)) :
    ∃ l : Fin m, SReaches C (n + m) (n + m + o) false (n + l.val) ∧
      SReaches C (n + m) (n + m + o) true (n + l.val) := by
  set N := n + m
  obtain ⟨l, hl⟩ := hColIncomp c0
  have heval_c : ∀ i : Fin n, A i c0 = (C.wires (bitVec {i} (∅ : Finset (Fin m)))).getD (N + o) false := by
    intro i
    rw [← hRep i c0, Circuit.eval, hout_eq, oneEach_eq_bitVec]
    apply wires_indep C N hF _ _ (bitVec_len _ _) (bitVec_len _ _) (N + o)
    intro w hw hwr
    by_cases h1 : w < n
    · rw [bitVec_getD_left ({i} : Finset (Fin n)) ({c0} : Finset (Fin m)) ⟨w, h1⟩,
          bitVec_getD_left ({i} : Finset (Fin n)) (∅ : Finset (Fin m)) ⟨w, h1⟩]
    · have h2 : w - n < m := by omega
      have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
      have hne : (⟨w - n, h2⟩ : Fin m) ≠ c0 := fun e => hnc0 (by rw [← e]; simpa [← hwe] using hwr)
      rw [hwe, bitVec_getD_right, bitVec_getD_right]
      simp [hne]
  have hflip : ∀ i : Fin n, evalOv C N (bitVec {i} (∅ : Finset (Fin m))) (n + l.val) true (N + o) = A i l := by
    intro i
    rw [← hRep i l, Circuit.eval, hout_eq, oneEach_eq_bitVec]
    have hlval : (C.wires (bitVec {i} {l})).getD (n + l.val) false = true := by
      rw [wires_getD_input C _ _ (by rw [bitVec_len]; omega), bitVec_getD_right]; simp
    rw [← evalOv_eq_wires C N (bitVec {i} {l}) (bitVec_len _ _) (n + l.val) (N + o), hlval]
    apply evalOv_indep C N hF _ _ (n + l.val) true (N + o)
    intro w hw hwa
    have hne : w ≠ n + l.val := reachesAvoid_ne hwa
    by_cases h1 : w < n
    · rw [bitVec_getD_left ({i} : Finset (Fin n)) (∅ : Finset (Fin m)) ⟨w, h1⟩,
          bitVec_getD_left ({i} : Finset (Fin n)) ({l} : Finset (Fin m)) ⟨w, h1⟩]
    · have h2 : w - n < m := by omega
      have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
      have hne' : (⟨w - n, h2⟩ : Fin m) ≠ l := fun e => hne (by rw [hwe, ← e])
      rw [hwe, bitVec_getD_right, bitVec_getD_right]
      simp [hne']
  have hzero : ∀ i : Fin n, evalOv C N (bitVec {i} (∅ : Finset (Fin m))) (n + l.val) false (N + o) = A i c0 := by
    intro i
    have hlval : (C.wires (bitVec {i} (∅ : Finset (Fin m)))).getD (n + l.val) false = false := by
      rw [wires_getD_input C _ _ (by rw [bitVec_len]; omega), bitVec_getD_right]; simp
    have h0 := evalOv_eq_wires C N (bitVec {i} (∅ : Finset (Fin m))) (bitVec_len _ _) (n + l.val) (N + o)
    rw [hlval] at h0
    rw [h0, ← heval_c i]
  refine ⟨l, ?_, ?_⟩
  · by_contra hnf
    apply hl; right; intro i hil
    have hle := (evalOv_mono C N hF (bitVec {i} (∅ : Finset (Fin m))) (n + l.val) (N + o)).2 hnf
    rw [hflip i, hzero i, hil] at hle
    exact Bool.eq_true_of_true_le hle
  · by_contra hnt
    apply hl; left; intro i hic
    have hle := (evalOv_mono C N hF (bitVec {i} (∅ : Finset (Fin m))) (n + l.val) (N + o)).1 hnt
    rw [hflip i, hzero i, hic] at hle
    exact Bool.eq_true_of_true_le hle

open Classical in
lemma main_proof (n m : ℕ) (A : Fin n → Fin m → Bool) (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hRowInj : Function.Injective A) (hColInj : Function.Injective (fun j i => A i j))
    (hRowIncomp : ∀ i : Fin n, ∃ k : Fin n,
      ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (hColIncomp : ∀ j : Fin m, ∃ l : Fin m,
      ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (C : Circuit) (hF : FanInTwo C) (hRep : Represents A C)
    (hSize : C.size ≤ n + m - 1)
    (hHasNot : ∃ gate ∈ C.gates, gate.op = GateOp.not) :
    ∃ (r : Fin n) (c : Fin m) (S : Finset (Fin n)) (T : Finset (Fin m))
      (W : Finset (Fin n) → Finset (Fin m) → Bool)
      (K : Finset (Fin n) → Finset (Fin m) → Bool → Bool),
      r ∉ S ∧ c ∉ T ∧ 2 ≤ S.card + T.card ∧
      (∀ i ∈ S, (∀ j, A r j = true → A i j = true) ∨ (∀ j, A i j = true → A r j = true)) ∧
      (∀ j ∈ T, (∀ i, A i c = true → A i j = true) ∨ (∀ i, A i j = true → A i c = true)) ∧
      (∀ l l' q q', l ⊆ l' → q ⊆ q' → W l q = true → W l' q' = true) ∧
      ∀ i j, A i j = K ({i} ∩ S) ({j} ∩ T) (W (({i} \ S).erase r) (({j} \ T).erase c)) := by
  set N := n + m
  obtain ⟨hout_ge, hout_lt⟩ := output_bounds A hn hm hRowInj hColInj C hRep
  set o := C.output - N
  have ho_lt : o < C.gates.length := by omega
  have hout_eq : C.output = N + o := by omega
  set G : Finset ℕ := (Finset.range C.gates.length).filter (fun g => Reaches C N (N + g) (N + o))
  set I_L : Finset (Fin n) := Finset.univ.filter (fun i => Reaches C N i.val (N + o))
  set I_R : Finset (Fin m) := Finset.univ.filter (fun j => Reaches C N (n + j.val) (N + o))
  set V_act : Finset ℕ := (Finset.range (N + C.gates.length)).filter (fun w => Reaches C N w (N + o))
  have ho_mem_G : o ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ho_lt, reaches_refl C N _⟩
  have ho_mem_V : N + o ∈ V_act :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), reaches_refl C N _⟩
  have hIL_ge : n - 1 ≤ I_L.card := by
    by_contra hlt
    have hcompl : 2 ≤ I_Lᶜ.card := by
      have hc := Finset.card_compl I_L
      simp only [Fintype.card_fin] at hc
      omega
    obtain ⟨i1, hi1, i2, hi2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < I_Lᶜ.card)
    have hni1 : ¬ Reaches C N i1.val (N + o) := by
      have := Finset.mem_compl.mp hi1
      simp only [I_L, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hni2 : ¬ Reaches C N i2.val (N + o) := by
      have := Finset.mem_compl.mp hi2
      simp only [I_L, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have heq : A i1 = A i2 := by
      funext j
      rw [← hRep i1 j, ← hRep i2 j]
      unfold Circuit.eval
      rw [hout_eq, oneEach_eq_bitVec, oneEach_eq_bitVec]
      apply wires_indep C N hF _ _ (bitVec_len _ _) (bitVec_len _ _) (N + o)
      intro w hw hwr
      by_cases h1 : w < n
      · have hwi : (⟨w, h1⟩ : Fin n) ≠ i1 ∧ (⟨w, h1⟩ : Fin n) ≠ i2 := by
          constructor
          · intro e; exact hni1 (by simpa [← e] using hwr)
          · intro e; exact hni2 (by simpa [← e] using hwr)
        rw [bitVec_getD_left ({i1} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩,
            bitVec_getD_left ({i2} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩]
        simp [hwi.1, hwi.2]
      · have h2 : w - n < m := by omega
        have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
        rw [hwe, bitVec_getD_right, bitVec_getD_right]
    exact hne (hRowInj heq)
  have hIR_ge : m - 1 ≤ I_R.card := by
    by_contra hlt
    have hcompl : 2 ≤ I_Rᶜ.card := by
      have hc := Finset.card_compl I_R
      simp only [Fintype.card_fin] at hc
      omega
    obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < I_Rᶜ.card)
    have hnj1 : ¬ Reaches C N (n + j1.val) (N + o) := by
      have := Finset.mem_compl.mp hj1
      simp only [I_R, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hnj2 : ¬ Reaches C N (n + j2.val) (N + o) := by
      have := Finset.mem_compl.mp hj2
      simp only [I_R, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have heq : (fun i => A i j1) = (fun i => A i j2) := by
      funext i
      rw [← hRep i j1, ← hRep i j2]
      unfold Circuit.eval
      rw [hout_eq, oneEach_eq_bitVec, oneEach_eq_bitVec]
      apply wires_indep C N hF _ _ (bitVec_len _ _) (bitVec_len _ _) (N + o)
      intro w hw hwr
      by_cases h1 : w < n
      · rw [bitVec_getD_left ({i} : Finset (Fin n)) ({j1} : Finset (Fin m)) ⟨w, h1⟩,
            bitVec_getD_left ({i} : Finset (Fin n)) ({j2} : Finset (Fin m)) ⟨w, h1⟩]
      · have h2 : w - n < m := by omega
        have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
        have hwj : (⟨w - n, h2⟩ : Fin m) ≠ j1 ∧ (⟨w - n, h2⟩ : Fin m) ≠ j2 := by
          constructor
          · intro e; apply hnj1; rw [← e]; simpa [← hwe] using hwr
          · intro e; apply hnj2; rw [← e]; simpa [← hwe] using hwr
        rw [hwe, bitVec_getD_right, bitVec_getD_right]
        simp [hwj.1, hwj.2]
    exact hne (hColInj heq)
  have hIL_le : I_L.card ≤ n := by simpa using Finset.card_le_univ I_L
  have hIR_le : I_R.card ≤ m := by simpa using Finset.card_le_univ I_R
  have hG_le : G.card ≤ C.gates.length := by
    calc G.card ≤ (Finset.range C.gates.length).card := Finset.card_filter_le _ _
      _ = C.gates.length := Finset.card_range _
  have hV_eq : V_act = (I_L.image Fin.val ∪ I_R.image (fun j : Fin m => n + j.val)) ∪
      G.image (fun g => N + g) := by
    ext w
    simp only [V_act, I_L, I_R, G, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hwlt, hwr⟩
      by_cases h1 : w < n
      · left; left; exact ⟨⟨w, h1⟩, hwr, rfl⟩
      · by_cases h2 : w < N
        · left; right; exact ⟨⟨w - n, by omega⟩, by simpa [show n + (w - n) = w by omega] using hwr, by simp; omega⟩
        · right; exact ⟨w - N, ⟨by omega, by simpa [show N + (w - N) = w by omega] using hwr⟩, by omega⟩
    · rintro ((⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨g, ⟨hg, hgr⟩, rfl⟩)
      · exact ⟨by have := i.isLt; omega, hi⟩
      · exact ⟨by have := j.isLt; omega, hj⟩
      · exact ⟨by omega, hgr⟩
  have hV_card : V_act.card = I_L.card + I_R.card + G.card := by
    rw [hV_eq, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
        Finset.card_image_of_injective _ Fin.val_injective,
        Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega)),
        Finset.card_image_of_injective _ (fun a b h => by omega)]
    · rw [Finset.disjoint_left]
      intro w hw1 hw2
      rcases Finset.mem_image.mp hw1 with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp hw2 with ⟨j, _, heq⟩
      have := i.isLt
      omega
    · rw [Finset.disjoint_left]
      intro w hw1 hw2
      rcases Finset.mem_image.mp hw2 with ⟨g, _, rfl⟩
      rcases Finset.mem_union.mp hw1 with hw1 | hw1
      · rcases Finset.mem_image.mp hw1 with ⟨i, _, heq⟩; have := i.isLt; omega
      · rcases Finset.mem_image.mp hw1 with ⟨j, _, heq⟩; have := j.isLt; omega
  set V_in := V_act.erase (N + o)
  have hVin_card : V_in.card = I_L.card + I_R.card + G.card - 1 := by
    rw [Finset.card_erase_of_mem ho_mem_V, hV_card]
  set readers : ℕ → Finset ℕ := fun w => G.filter (fun g => w ∈ effSet C N g)
  have hreaders_pos : ∀ w ∈ V_in, 1 ≤ (readers w).card := by
    intro w hw
    obtain ⟨hne, hmemV⟩ := Finset.mem_erase.mp hw
    obtain ⟨_, s, hs⟩ := Finset.mem_filter.mp hmemV
    cases hs with
    | refl => exact absurd rfl hne
    | step hg hu hrest =>
      apply Finset.card_pos.mpr
      refine ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg, ⟨_, hrest⟩⟩, hu⟩⟩
  have hdouble : ∑ w ∈ V_in, (readers w).card = ∑ g ∈ G, (effSet C N g).card := by
    have h1 : ∑ w ∈ V_in, (readers w).card =
        ∑ w ∈ V_in, ∑ g ∈ G, if w ∈ effSet C N g then 1 else 0 := by
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.card_filter]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g hg => ?_
    have hg_lt : g < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hg).1
    have hg_r : Reaches C N (N + g) (N + o) := (Finset.mem_filter.mp hg).2
    have hsub : effSet C N g ⊆ V_in := by
      intro w hw
      have hwlt := effSet_lt C N g w hw
      have hgle := reaches_le hg_r
      refine Finset.mem_erase.mpr ⟨by omega, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      exact reaches_step hg_lt hw hg_r
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub,
        Finset.sum_const, smul_eq_mul, mul_one]
  set G_not := G.filter (fun g => gateSign C g = true)
  set F := ∑ w ∈ V_in, ((readers w).card - 1)
  set slack := ∑ g ∈ G, ((if gateSign C g = true then 1 else 2) - (effSet C N g).card)
  have hsum_eff : (∑ g ∈ G, (effSet C N g).card) + slack + G_not.card = 2 * G.card := by
    have hcap : ∀ g ∈ G, (effSet C N g).card ≤ if gateSign C g = true then 1 else 2 := by
      intro g hg
      have hg_lt : g < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hg).1
      split_ifs with hgs
      · exact effSet_card_not C N g hg_lt ((gateSign_eq_true_iff C g hg_lt).mp hgs)
      · exact effSet_card_le_two C N g hF hg_lt
    have h1 : (∑ g ∈ G, (effSet C N g).card) + slack =
        ∑ g ∈ G, if gateSign C g = true then 1 else 2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun g hg => Nat.add_sub_cancel' (hcap g hg)
    have h2 : (∑ g ∈ G, if gateSign C g = true then 1 else 2) + G_not.card = 2 * G.card := by
      have hgn : G_not.card = ∑ g ∈ G, if gateSign C g = true then 1 else 0 := Finset.card_filter _ _
      rw [hgn, ← Finset.sum_add_distrib]
      have h3 : ∑ g ∈ G, ((if gateSign C g = true then 1 else 2) + if gateSign C g = true then 1 else 0) =
          ∑ _g ∈ G, 2 := Finset.sum_congr rfl fun g _ => by split_ifs <;> rfl
      rw [h3, Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  have hsum_deg : F + V_in.card = ∑ w ∈ V_in, (readers w).card :=
    sum_sub_one_add_card V_in (fun w => (readers w).card) hreaders_pos
  have hbudget : G_not.card + F + slack + (C.gates.length - G.card) ≤ (n - I_L.card) + (m - I_R.card) := by
    have hsz : C.gates.length ≤ n + m - 1 := hSize
    have hVpos : 1 ≤ I_L.card + I_R.card + G.card := by
      have : 1 ≤ G.card := Finset.card_pos.mpr ⟨o, ho_mem_G⟩
      omega
    omega
  have hbinate_left : ∀ r0 : Fin n, r0 ∉ I_L →
      ∃ k : Fin n, SReaches C N (N + o) false k.val ∧ SReaches C N (N + o) true k.val := by
    intro r0 hr0
    have hnr0 : ¬ Reaches C N r0.val (N + o) := by
      simp only [I_L, Finset.mem_filter, Finset.mem_univ, true_and] at hr0; exact hr0
    exact binate_left_of_omitted A hRowIncomp C hF hRep o hout_eq r0 hnr0
  have hbinate_right : ∀ c0 : Fin m, c0 ∉ I_R →
      ∃ l : Fin m, SReaches C N (N + o) false (n + l.val) ∧ SReaches C N (N + o) true (n + l.val) := by
    intro c0 hc0
    have hnc0 : ¬ Reaches C N (n + c0.val) (N + o) := by
      simp only [I_R, Finset.mem_filter, Finset.mem_univ, true_and] at hc0; exact hc0
    exact binate_right_of_omitted A hColIncomp C hF hRep o hout_eq c0 hnc0
  have hGnot_pos : 1 ≤ G_not.card := by
    by_contra h0
    have hgn0 : G_not.card = 0 := by omega
    have hno_not_G : ∀ g ∈ G, gateSign C g = false := by
      intro g hg
      cases hgs : gateSign C g with
      | false => rfl
      | true =>
        have hmem : g ∈ G_not := Finset.mem_filter.mpr ⟨hg, hgs⟩
        have := Finset.card_pos.mpr ⟨g, hmem⟩
        omega
    obtain ⟨gate0, hgate0_mem, hgate0_not⟩ := hHasNot
    obtain ⟨idx0, hidx0_lt, hidx0_eq⟩ := List.mem_iff_getElem.mp hgate0_mem
    have hidx0_notG : idx0 ∉ G := by
      intro hmem
      have hgs := hno_not_G idx0 hmem
      have hgs' := (gateSign_eq_true_iff C idx0 hidx0_lt).mpr (by rw [hidx0_eq]; exact hgate0_not)
      rw [hgs] at hgs'; cases hgs'
    have hdead : 1 ≤ C.gates.length - G.card := by
      have hsub : G ⊆ (Finset.range C.gates.length).erase idx0 := by
        intro g hg
        exact Finset.mem_erase.mpr ⟨fun e => hidx0_notG (e ▸ hg), (Finset.mem_filter.mp hg).1⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hidx0_lt), Finset.card_range] at hc
      omega
    have hno_sreach_true : ∀ u : ℕ, ¬ SReaches C N (N + o) true u := by
      intro u hs
      have haux : ∀ s v, SReaches C N (N + o) s v → s = false := by
        intro s v h
        induction h with
        | refl => rfl
        | step hg hu hrest ih =>
          have hmemG : _ ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg, ⟨_, hrest⟩⟩
          rw [hno_not_G _ hmemG, ih]
          rfl
      have := haux true u hs
      cases this
    have homit : I_L.card < n ∨ I_R.card < m := by omega
    rcases homit with hL | hR
    · have hne : I_Lᶜ.Nonempty := Finset.card_pos.mp (by have := Finset.card_compl I_L; simp at this; omega)
      obtain ⟨r0, hr0⟩ := hne
      obtain ⟨k, _, hkt⟩ := hbinate_left r0 (Finset.mem_compl.mp hr0)
      exact hno_sreach_true k.val hkt
    · have hne : I_Rᶜ.Nonempty := Finset.card_pos.mp (by have := Finset.card_compl I_R; simp at this; omega)
      obtain ⟨c0, hc0⟩ := hne
      obtain ⟨l, _, hlt⟩ := hbinate_right c0 (Finset.mem_compl.mp hc0)
      exact hno_sreach_true (n + l.val) hlt
  have hF_pos : 1 ≤ F := by
    by_contra h0
    have hF0 : F = 0 := by omega
    have hdeg1 : ∀ w ∈ V_in, (readers w).card = 1 := by
      intro w hw
      have hsub0 : (readers w).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp hF0) w hw
      have hpos := hreaders_pos w hw
      omega
    have huniq : ∀ s1 u, SReaches C N (N + o) s1 u → ∀ s2, SReaches C N (N + o) s2 u → s1 = s2 := by
      intro s1 u h1
      induction h1 with
      | refl => intro s2 h2; exact (sreaches_refl_eq h2).symm
      | step hg1 hu1 hrest1 ih =>
        rename_i sa u1 w1
        intro s2 h2
        have hlt1 := effSet_lt C N w1 u1 hu1
        have hle1 := sreaches_le hrest1
        cases h2 with
        | refl => omega
        | step hg2 hu2 hrest2 =>
          rename_i sb w2
          have hu1_in : u1 ∈ V_in :=
            Finset.mem_erase.mpr ⟨by omega, Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr (by omega), ⟨_, SReaches.step hg1 hu1 hrest1⟩⟩⟩
          have hw1_r : w1 ∈ readers u1 :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg1, ⟨_, hrest1⟩⟩, hu1⟩
          have hw2_r : w2 ∈ readers u1 :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg2, ⟨_, hrest2⟩⟩, hu2⟩
          have hle_one : (readers u1).card ≤ 1 := Nat.le_of_eq (hdeg1 u1 hu1_in)
          have heqw : w1 = w2 := Finset.card_le_one.mp hle_one w1 hw1_r w2 hw2_r
          subst heqw
          rw [ih _ hrest2]
    have homit : I_L.card < n ∨ I_R.card < m := by omega
    rcases homit with hL | hR
    · have hne : I_Lᶜ.Nonempty := Finset.card_pos.mp (by have := Finset.card_compl I_L; simp at this; omega)
      obtain ⟨r0, hr0⟩ := hne
      obtain ⟨k, hkf, hkt⟩ := hbinate_left r0 (Finset.mem_compl.mp hr0)
      have := huniq false k.val hkf true hkt
      cases this
    · have hne : I_Rᶜ.Nonempty := Finset.card_pos.mp (by have := Finset.card_compl I_R; simp at this; omega)
      obtain ⟨c0, hc0⟩ := hne
      obtain ⟨l, hlf, hlt⟩ := hbinate_right c0 (Finset.mem_compl.mp hc0)
      have := huniq false (n + l.val) hlf true hlt
      cases this
  have hGnot_eq : G_not.card = 1 := by omega
  have hF_eq : F = 1 := by omega
  have hIL_eq : I_L.card + 1 = n := by omega
  have hIR_eq : I_R.card + 1 = m := by omega
  obtain ⟨r, hr_not, _⟩ := card_eq_sub_one_exists_missing I_L (by simpa using hIL_eq)
  obtain ⟨c, hc_not, _⟩ := card_eq_sub_one_exists_missing I_R (by simpa using hIR_eq)
  obtain ⟨f, hf_in, _, hf_other⟩ := unique_of_sum_eq_one V_in (fun w => (readers w).card - 1) hF_eq
  have hf_lt_o : f < N + o := by
    have hne : f ≠ N + o := (Finset.mem_erase.mp hf_in).1
    have hle : f ≤ N + o := reaches_le (Finset.mem_filter.mp (Finset.mem_erase.mp hf_in).2).2
    omega
  have hf_reaches_o : Reaches C N f (N + o) := (Finset.mem_filter.mp (Finset.mem_erase.mp hf_in).2).2
  have hdeg_other : ∀ w ∈ V_in, w ≠ f → (readers w).card = 1 := by
    intro w hw hne
    have h0 := hf_other w hw hne
    have hpos := hreaders_pos w hw
    omega
  have hnext_eq : ∀ u w1 w2, u ≠ f → u < N + o →
      w1 < C.gates.length → u ∈ effSet C N w1 → Reaches C N (N + w1) (N + o) →
      w2 < C.gates.length → u ∈ effSet C N w2 → Reaches C N (N + w2) (N + o) →
      w1 = w2 := by
    intro u w1 w2 hnef hult hg1 hu1 hr1 hg2 hu2 hr2
    have hu_in : u ∈ V_in :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), reaches_step hg1 hu1 hr1⟩⟩
    have hw1_r : w1 ∈ readers u :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg1, hr1⟩, hu1⟩
    have hw2_r : w2 ∈ readers u :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg2, hr2⟩, hu2⟩
    have hle_one : (readers u).card ≤ 1 := Nat.le_of_eq (hdeg_other u hu_in hnef)
    exact Finset.card_le_one.mp hle_one w1 hw1_r w2 hw2_r
  have huniq_not_f : ∀ s1 u, SReaches C N (N + o) s1 u → ¬ Reaches C N u f →
      ∀ s2, SReaches C N (N + o) s2 u → s1 = s2 := by
    intro s1 u h1
    induction h1 with
    | refl => intro _ s2 h2; exact (sreaches_refl_eq h2).symm
    | step hg1 hu1 hrest1 ih =>
      rename_i sa u1 w1
      intro hnf s2 h2
      have hlt1 := effSet_lt C N w1 u1 hu1
      have hle1 := sreaches_le hrest1
      have hnef : u1 ≠ f := fun e => hnf (by rw [e]; exact reaches_refl C N f)
      cases h2 with
      | refl => omega
      | step hg2 hu2 hrest2 =>
        rename_i sb w2
        have heqw := hnext_eq u1 w1 w2 hnef (by omega) hg1 hu1 ⟨_, hrest1⟩ hg2 hu2 ⟨_, hrest2⟩
        subst heqw
        have hnf' : ¬ Reaches C N (N + w1) f := fun hr => hnf (reaches_step hg1 hu1 hr)
        rw [ih hnf' _ hrest2]
  have huniq_to_f : ∀ s1 u, SReaches C N f s1 u → ∀ s2, SReaches C N f s2 u → s1 = s2 := by
    intro s1 u h1
    induction h1 with
    | refl => intro s2 h2; exact (sreaches_refl_eq h2).symm
    | step hg1 hu1 hrest1 ih =>
      rename_i sa u1 w1
      intro s2 h2
      have hlt1 := effSet_lt C N w1 u1 hu1
      have hle1 := sreaches_le hrest1
      cases h2 with
      | refl => omega
      | step hg2 hu2 hrest2 =>
        rename_i sb w2
        have hr1 : Reaches C N (N + w1) (N + o) := reaches_trans ⟨_, hrest1⟩ hf_reaches_o
        have hr2 : Reaches C N (N + w2) (N + o) := reaches_trans ⟨_, hrest2⟩ hf_reaches_o
        have heqw := hnext_eq u1 w1 w2 (by omega) (by omega) hg1 hu1 hr1 hg2 hu2 hr2
        subst heqw
        rw [ih _ hrest2]
  have hsplit_f : ∀ s u, SReaches C N (N + o) s u → Reaches C N u f →
      ∃ s1 s2, SReaches C N f s1 u ∧ SReaches C N (N + o) s2 f ∧ s = xor s1 s2 := by
    intro s u hs
    induction hs with
    | refl =>
      intro hrf
      have := reaches_le hrf
      omega
    | step hg1 hu1 hrest1 ih =>
      rename_i sa u1 w1
      intro hrf
      by_cases huf : u1 = f
      · subst huf
        exact ⟨false, _, SReaches.refl, SReaches.step hg1 hu1 hrest1, by simp⟩
      · obtain ⟨sf, hsf⟩ := hrf
        cases hsf with
        | refl => exact absurd rfl huf
        | step hg2 hu2 hrest2 =>
          rename_i sb w2
          have hlt1 := effSet_lt C N w1 u1 hu1
          have hle1 := sreaches_le hrest1
          have hr2 : Reaches C N (N + w2) (N + o) := reaches_trans ⟨_, hrest2⟩ hf_reaches_o
          have heqw := hnext_eq u1 w1 w2 huf (by omega) hg1 hu1 ⟨_, hrest1⟩ hg2 hu2 hr2
          subst heqw
          obtain ⟨s1, s2, hs1, hs2, heq⟩ := ih ⟨_, hrest2⟩
          refine ⟨xor (gateSign C w1) s1, s2, SReaches.step hg1 hu1 hs1, hs2, ?_⟩
          rw [heq, Bool.xor_assoc]
  have hnot_avoid_of_reaches : ∀ u, ReachesAvoid C N f (N + o) u → ¬ Reaches C N u f := by
    intro u hav
    induction hav with
    | refl _ =>
      intro hrf
      have := reaches_le hrf
      omega
    | step hu hg1 hmem1 hrest1 ih =>
      rename_i u1 w1
      intro hrf
      obtain ⟨sf, hsf⟩ := hrf
      cases hsf with
      | refl => exact hu rfl
      | step hg2 hu2 hrest2 =>
        rename_i sb w2
        have hlt1 := effSet_lt C N w1 u1 hmem1
        have hr1 : Reaches C N (N + w1) (N + o) := reachesAvoid_reaches hrest1
        have hle1 := reaches_le hr1
        have hr2 : Reaches C N (N + w2) (N + o) := reaches_trans ⟨_, hrest2⟩ hf_reaches_o
        have heqw := hnext_eq u1 w1 w2 hu (by omega) hg1 hmem1 hr1 hg2 hu2 hr2
        subst heqw
        exact ih ⟨_, hrest2⟩
  have hnoNot_cone_f : ∀ (g : ℕ) (hg : g < C.gates.length),
      Reaches C N (N + g) f → (C.gates[g]'hg).op ≠ GateOp.not := by
    intro g hg hgf hnot
    have hg_Gnot : g ∈ G_not :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg, reaches_trans hgf hf_reaches_o⟩,
         (gateSign_eq_true_iff C g hg).mpr hnot⟩
    have hgt_f_false : ∀ s v, SReaches C N (N + o) s v → f ≤ v → s = false := by
      intro s v hsv
      induction hsv with
      | refl => intro _; rfl
      | step hg1 hu1 hrest1 ih =>
        rename_i sa u1 w1
        intro hfv
        have hlt1 := effSet_lt C N w1 u1 hu1
        have hle_g := reaches_le hgf
        have hne_g : w1 ≠ g := by omega
        have hgs_f : gateSign C w1 = false := by
          cases hgs : gateSign C w1 with
          | false => rfl
          | true =>
            have hw1_Gnot : w1 ∈ G_not :=
              Finset.mem_filter.mpr
                ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg1, ⟨_, hrest1⟩⟩, hgs⟩
            exact absurd (Finset.card_le_one.mp (Nat.le_of_eq hGnot_eq) w1 hw1_Gnot g hg_Gnot) hne_g
        rw [hgs_f, ih (by omega)]
        rfl
    obtain ⟨k, hkf, hkt⟩ := hbinate_left r hr_not
    have hkrf : Reaches C N k.val f := by
      by_contra hnf
      have := huniq_not_f false k.val hkf hnf true hkt
      cases this
    obtain ⟨s1, s2, hs1, hs2, heq1⟩ := hsplit_f false k.val hkf hkrf
    obtain ⟨t1, t2, ht1, ht2, heq2⟩ := hsplit_f true k.val hkt hkrf
    have hs2f := hgt_f_false s2 f hs2 le_rfl
    have ht2f := hgt_f_false t2 f ht2 le_rfl
    have hst1 := huniq_to_f s1 k.val hs1 t1 ht1
    rw [hs2f, Bool.xor_false] at heq1
    rw [ht2f, Bool.xor_false, ← hst1] at heq2
    rw [← heq1] at heq2
    cases heq2
  set S : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => ReachesAvoid C N f (N + o) i.val)
  set T : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => ReachesAvoid C N f (N + o) (n + j.val))
  set W : Finset (Fin n) → Finset (Fin m) → Bool := fun L Q => (C.wires (bitVec L Q)).getD f false
  set K : Finset (Fin n) → Finset (Fin m) → Bool → Bool := fun L Q b => evalOv C N (bitVec L Q) f b (N + o)
  have hr_not_S : r ∉ S := by
    intro hmem
    have hav := (Finset.mem_filter.mp hmem).2
    exact hr_not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, reachesAvoid_reaches hav⟩)
  have hc_not_T : c ∉ T := by
    intro hmem
    have hav := (Finset.mem_filter.mp hmem).2
    exact hc_not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, reachesAvoid_reaches hav⟩)
  have hS_comp : ∀ i ∈ S, (∀ j, A r j = true → A i j = true) ∨ (∀ j, A i j = true → A r j = true) := by
    intro i hi
    have hav : ReachesAvoid C N f (N + o) i.val := (Finset.mem_filter.mp hi).2
    have hnf : ¬ Reaches C N i.val f := hnot_avoid_of_reaches i.val hav
    have hnot_both : ¬ (SReaches C N (N + o) false i.val ∧ SReaches C N (N + o) true i.val) := by
      rintro ⟨h1, h2⟩
      have := huniq_not_f false i.val h1 hnf true h2
      cases this
    have hnr : ¬ Reaches C N r.val (N + o) := by
      simp only [I_L, Finset.mem_filter, Finset.mem_univ, true_and] at hr_not; exact hr_not
    have hstep_eval : ∀ j : Fin m,
        evalOv C N (bitVec (∅ : Finset (Fin n)) {j}) i.val false (N + o) = A r j ∧
        evalOv C N (bitVec (∅ : Finset (Fin n)) {j}) i.val true (N + o) = A i j := by
      intro j
      constructor
      · have hzero : (C.wires (bitVec (∅ : Finset (Fin n)) {j})).getD i.val false = false := by
          rw [wires_getD_input C _ _ (by rw [bitVec_len]; omega), bitVec_getD_left]; simp
        have h0 := evalOv_eq_wires C N (bitVec (∅ : Finset (Fin n)) {j}) (bitVec_len _ _) i.val (N + o)
        rw [hzero] at h0
        rw [h0, ← hRep r j, Circuit.eval, hout_eq, oneEach_eq_bitVec]
        apply wires_indep C N hF _ _ (bitVec_len _ _) (bitVec_len _ _) (N + o)
        intro w hw hwr
        by_cases h1 : w < n
        · have hne : (⟨w, h1⟩ : Fin n) ≠ r := fun e => hnr (by simpa [← e] using hwr)
          rw [bitVec_getD_left (∅ : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩,
              bitVec_getD_left ({r} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩]
          simp [hne]
        · have h2 : w - n < m := by omega
          have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
          rw [hwe, bitVec_getD_right, bitVec_getD_right]
      · rw [← hRep i j, Circuit.eval, hout_eq, oneEach_eq_bitVec]
        have hival : (C.wires (bitVec {i} {j})).getD i.val false = true := by
          rw [wires_getD_input C _ _ (by rw [bitVec_len]; omega), bitVec_getD_left]; simp
        rw [← evalOv_eq_wires C N (bitVec {i} {j}) (bitVec_len _ _) i.val (N + o), hival]
        apply evalOv_indep C N hF _ _ i.val true (N + o)
        intro w hw hwa
        have hne : w ≠ i.val := reachesAvoid_ne hwa
        by_cases h1 : w < n
        · have hne' : (⟨w, h1⟩ : Fin n) ≠ i := fun e => hne (congrArg Fin.val e)
          rw [bitVec_getD_left (∅ : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩,
              bitVec_getD_left ({i} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩]
          simp [hne']
        · have h2 : w - n < m := by omega
          have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
          rw [hwe, bitVec_getD_right, bitVec_getD_right]
    by_cases hnt : SReaches C N (N + o) true i.val
    · have hnf' : ¬ SReaches C N (N + o) false i.val := fun h => hnot_both ⟨h, hnt⟩
      right
      intro j hij
      have hle := (evalOv_mono C N hF (bitVec (∅ : Finset (Fin n)) {j}) i.val (N + o)).2 hnf'
      rw [(hstep_eval j).1, (hstep_eval j).2, hij] at hle
      exact Bool.eq_true_of_true_le hle
    · left
      intro j hrj
      have hle := (evalOv_mono C N hF (bitVec (∅ : Finset (Fin n)) {j}) i.val (N + o)).1 hnt
      rw [(hstep_eval j).1, (hstep_eval j).2, hrj] at hle
      exact Bool.eq_true_of_true_le hle
  have hT_comp : ∀ j ∈ T, (∀ i, A i c = true → A i j = true) ∨ (∀ i, A i j = true → A i c = true) := by
    intro j hj
    have hav : ReachesAvoid C N f (N + o) (n + j.val) := (Finset.mem_filter.mp hj).2
    have hnf : ¬ Reaches C N (n + j.val) f := hnot_avoid_of_reaches (n + j.val) hav
    have hnot_both : ¬ (SReaches C N (N + o) false (n + j.val) ∧ SReaches C N (N + o) true (n + j.val)) := by
      rintro ⟨h1, h2⟩
      have := huniq_not_f false (n + j.val) h1 hnf true h2
      cases this
    have hnc : ¬ Reaches C N (n + c.val) (N + o) := by
      simp only [I_R, Finset.mem_filter, Finset.mem_univ, true_and] at hc_not; exact hc_not
    have hstep_eval : ∀ i : Fin n,
        evalOv C N (bitVec {i} (∅ : Finset (Fin m))) (n + j.val) false (N + o) = A i c ∧
        evalOv C N (bitVec {i} (∅ : Finset (Fin m))) (n + j.val) true (N + o) = A i j := by
      intro i
      constructor
      · have hzero : (C.wires (bitVec {i} (∅ : Finset (Fin m)))).getD (n + j.val) false = false := by
          rw [wires_getD_input C _ _ (by rw [bitVec_len]; omega), bitVec_getD_right]; simp
        have h0 := evalOv_eq_wires C N (bitVec {i} (∅ : Finset (Fin m))) (bitVec_len _ _) (n + j.val) (N + o)
        rw [hzero] at h0
        rw [h0, ← hRep i c, Circuit.eval, hout_eq, oneEach_eq_bitVec]
        apply wires_indep C N hF _ _ (bitVec_len _ _) (bitVec_len _ _) (N + o)
        intro w hw hwr
        by_cases h1 : w < n
        · rw [bitVec_getD_left ({i} : Finset (Fin n)) (∅ : Finset (Fin m)) ⟨w, h1⟩,
              bitVec_getD_left ({i} : Finset (Fin n)) ({c} : Finset (Fin m)) ⟨w, h1⟩]
        · have h2 : w - n < m := by omega
          have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
          have hne : (⟨w - n, h2⟩ : Fin m) ≠ c := fun e => hnc (by rw [← e]; simpa [← hwe] using hwr)
          rw [hwe, bitVec_getD_right, bitVec_getD_right]
          simp [hne]
      · rw [← hRep i j, Circuit.eval, hout_eq, oneEach_eq_bitVec]
        have hjval : (C.wires (bitVec {i} {j})).getD (n + j.val) false = true := by
          rw [wires_getD_input C _ _ (by rw [bitVec_len]; omega), bitVec_getD_right]; simp
        rw [← evalOv_eq_wires C N (bitVec {i} {j}) (bitVec_len _ _) (n + j.val) (N + o), hjval]
        apply evalOv_indep C N hF _ _ (n + j.val) true (N + o)
        intro w hw hwa
        have hne : w ≠ n + j.val := reachesAvoid_ne hwa
        by_cases h1 : w < n
        · rw [bitVec_getD_left ({i} : Finset (Fin n)) (∅ : Finset (Fin m)) ⟨w, h1⟩,
              bitVec_getD_left ({i} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩]
        · have h2 : w - n < m := by omega
          have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
          have hne' : (⟨w - n, h2⟩ : Fin m) ≠ j := fun e => hne (by rw [hwe, ← e])
          rw [hwe, bitVec_getD_right, bitVec_getD_right]
          simp [hne']
    by_cases hnt : SReaches C N (N + o) true (n + j.val)
    · have hnf' : ¬ SReaches C N (N + o) false (n + j.val) := fun h => hnot_both ⟨h, hnt⟩
      right
      intro i hij
      have hle := (evalOv_mono C N hF (bitVec {i} (∅ : Finset (Fin m))) (n + j.val) (N + o)).2 hnf'
      rw [(hstep_eval i).1, (hstep_eval i).2, hij] at hle
      exact Bool.eq_true_of_true_le hle
    · left
      intro i hic
      have hle := (evalOv_mono C N hF (bitVec {i} (∅ : Finset (Fin m))) (n + j.val) (N + o)).1 hnt
      rw [(hstep_eval i).1, (hstep_eval i).2, hic] at hle
      exact Bool.eq_true_of_true_le hle
  have hW_mono : ∀ l l' q q', l ⊆ l' → q ⊆ q' → W l q = true → W l' q' = true := by
    intro l l' q q' hll hqq htrue
    have hle : W l q ≤ W l' q' := by
      apply wires_mono_cone C N hF _ _ (bitVec_len _ _) (bitVec_len _ _) f hnoNot_cone_f
      intro w hw _
      by_cases h1 : w < n
      · rw [bitVec_getD_left l q ⟨w, h1⟩, bitVec_getD_left l' q' ⟨w, h1⟩]
        by_cases hmem : (⟨w, h1⟩ : Fin n) ∈ l
        · simp [hmem, hll hmem]
        · simp [hmem]
      · have h2 : w - n < m := by omega
        have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
        rw [hwe, bitVec_getD_right l q ⟨w - n, h2⟩, bitVec_getD_right l' q' ⟨w - n, h2⟩]
        by_cases hmem : (⟨w - n, h2⟩ : Fin m) ∈ q
        · simp [hmem, hqq hmem]
        · simp [hmem]
    rw [htrue] at hle
    exact Bool.eq_true_of_true_le hle
  have hfactor : ∀ i j, A i j = K ({i} ∩ S) ({j} ∩ T) (W (({i} \ S).erase r) (({j} \ T).erase c)) := by
    intro i j
    have hWf : (C.wires (bitVec {i} {j})).getD f false = W (({i} \ S).erase r) (({j} \ T).erase c) := by
      apply wires_indep C N hF _ _ (bitVec_len _ _) (bitVec_len _ _) f
      intro w hw hwf
      by_cases h1 : w < n
      · rw [bitVec_getD_left ({i} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩,
            bitVec_getD_left (({i} \ S).erase r) (({j} \ T).erase c) ⟨w, h1⟩]
        have hnotS : (⟨w, h1⟩ : Fin n) ∉ S := fun hmem =>
          hnot_avoid_of_reaches w (Finset.mem_filter.mp hmem).2 hwf
        have hne_r : (⟨w, h1⟩ : Fin n) ≠ r := by
          intro e
          have hr_r : Reaches C N r.val (N + o) := by
            rw [← e]; exact reaches_trans hwf hf_reaches_o
          exact hr_not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_r⟩)
        simp [hnotS, hne_r]
      · have h2 : w - n < m := by omega
        have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
        rw [hwe, bitVec_getD_right ({i} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w - n, h2⟩,
            bitVec_getD_right (({i} \ S).erase r) (({j} \ T).erase c) ⟨w - n, h2⟩]
        have hnotT : (⟨w - n, h2⟩ : Fin m) ∉ T := fun hmem =>
          hnot_avoid_of_reaches w (by simpa [← hwe] using (Finset.mem_filter.mp hmem).2) hwf
        have hne_c : (⟨w - n, h2⟩ : Fin m) ≠ c := by
          intro e
          have hc_r : Reaches C N (n + c.val) (N + o) := by
            rw [← e, ← hwe]; exact reaches_trans hwf hf_reaches_o
          exact hc_not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_r⟩)
        simp [hnotT, hne_c]
    rw [← hRep i j, Circuit.eval, hout_eq, oneEach_eq_bitVec,
        ← evalOv_eq_wires C N (bitVec {i} {j}) (bitVec_len _ _) f (N + o), hWf]
    apply evalOv_indep C N hF _ _ f _ (N + o)
    intro w hw hwa
    by_cases h1 : w < n
    · have hmemS : (⟨w, h1⟩ : Fin n) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwa⟩
      rw [bitVec_getD_left ({i} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w, h1⟩,
          bitVec_getD_left ({i} ∩ S) ({j} ∩ T) ⟨w, h1⟩]
      simp [hmemS]
    · have h2 : w - n < m := by omega
      have hwe : w = n + (⟨w - n, h2⟩ : Fin m).val := by simp; omega
      have hmemT : (⟨w - n, h2⟩ : Fin m) ∈ T :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [← hwe] using hwa⟩
      rw [hwe, bitVec_getD_right ({i} : Finset (Fin n)) ({j} : Finset (Fin m)) ⟨w - n, h2⟩,
          bitVec_getD_right ({i} ∩ S) ({j} ∩ T) ⟨w - n, h2⟩]
      simp [hmemT]
  have hST_ge : 2 ≤ S.card + T.card :=
    st_card_ge_two A hRowIncomp hColIncomp r c S T W K hr_not_S hc_not_T hS_comp hT_comp hW_mono hfactor
  exact ⟨r, c, S, T, W, K, hr_not_S, hc_not_T, hST_ge, hS_comp, hT_comp, hW_mono, hfactor⟩

end PEqualNP.Outside.L_meta_25901_aux

theorem PEqualNP.Outside.L_meta_25901 :
  ∀ (n m : Nat) (A : Fin n → Fin m → Bool), 3 ≤ n → 3 ≤ m →
  let rowLE := fun i k : Fin n => ∀ j, A i j = true → A k j = true
  let colLE := fun j l : Fin m => ∀ i, A i j = true → A i l = true
  let rc := fun i k : Fin n => rowLE i k ∨ rowLE k i
  let cc := fun j l : Fin m => colLE j l ∨ colLE l j
  Function.Injective A → Function.Injective (fun j i => A i j) →
  (∀ i, ∃ k, ¬ rc i k) → (∀ j, ∃ l, ¬ cc j l) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
  C.size ≤ n + m - 1 →
  (∃ gate ∈ C.gates, gate.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
  ∃ (r : Fin n) (c : Fin m) (S : Finset (Fin n)) (T : Finset (Fin m))
    (W : Finset (Fin n) → Finset (Fin m) → Bool)
    (K : Finset (Fin n) → Finset (Fin m) → Bool → Bool),
    r ∉ S ∧ c ∉ T ∧ 2 ≤ S.card + T.card ∧
    (∀ i ∈ S, rc r i) ∧ (∀ j ∈ T, cc c j) ∧
    (∀ l l' q q', l ⊆ l' → q ⊆ q' → W l q = true → W l' q' = true) ∧
    ∀ i j, let x : Finset (Fin n) := {i}
           let y : Finset (Fin m) := {j}
           A i j = K (x ∩ S) (y ∩ T) (W ((x \ S).erase r) ((y \ T).erase c)) := by
  intro n m A hn hm rowLE colLE rc cc hRowInj hColInj hRowIncomp hColIncomp C hF hRep hSize hHasNot
  exact PEqualNP.Outside.L_meta_25901_aux.main_proof n m A hn hm hRowInj hColInj hRowIncomp hColIncomp C hF hRep hSize hHasNot
