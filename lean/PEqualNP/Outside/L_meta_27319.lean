import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27319

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def ext2 (y : Fin 7 → Bool) : Fin 9 → Bool :=
  Fin.cons false (Fin.cons true y)

def f01 (y : Fin 7 → Bool) : Bool := pm3 (ext2 y)

lemma getElem_zero_of_head? {α : Type*} {l : List α} {x : α} (h : l.head? = some x)
    (h0 : 0 < l.length) : l[0]'h0 = x := by
  cases l with
  | nil => simp at h
  | cons a t => simp only [List.head?_cons, Option.some.injEq] at h; simpa using h

lemma getElem_one_of_tail_head? {α : Type*} {l : List α} {x : α} (h : l.tail.head? = some x)
    (h1 : 1 < l.length) : l[1]'h1 = x := by
  cases l with
  | nil => simp at h1
  | cons a t =>
    cases t with
    | nil => simp at h1
    | cons b t' => simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at h; simpa using h

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma wires_eq_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

lemma W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

lemma W_append (a b : List Gate) (w : List Bool) :
    W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

lemma W_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma W_len (gs : List Gate) : ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

lemma getD_append_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_append_lt w _ i hi

lemma W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
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
      rw [show (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) from
        getD_append_len w _]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (getD_append_lt w _ i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      rw [step_len] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def wval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval
  rw [wires_eq_W, W_prefix C.gates (List.ofFn x) i (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

lemma wval_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hback : ∀ a ∈ (C.gates[j]).inputs, a < n + j) :
    wval C x (n + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun a => wval C x a) := by
  unfold wval
  rw [wires_eq_W]
  have h := W_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn] at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [if_pos (hback a ha)]

def WellStructured (n : ℕ) (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length,
    ((C.gates.get j).op = GateOp.not ∧ ∃ a, a < n + j.val ∧ (C.gates.get j).inputs = [a]) ∨
    (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
      ∃ a b, a < n + j.val ∧ b < n + j.val ∧ (C.gates.get j).inputs = [a, b])

lemma ws_back {n : ℕ} {C : Circuit} (hws : WellStructured n C) (j : ℕ) (hj : j < C.gates.length) :
    ∀ a ∈ (C.gates[j]).inputs, a < n + j := by
  intro a ha
  rcases hws ⟨j, hj⟩ with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
  · simp only [List.get_eq_getElem] at hins hu
    rw [hins, List.mem_singleton] at ha
    omega
  · simp only [List.get_eq_getElem] at hins hu hv
    rw [hins, List.mem_cons, List.mem_singleton] at ha
    rcases ha with rfl | rfl <;> omega

lemma f01_essential (i : Fin 7) :
    ∃ y : Fin 7 → Bool, f01 y ≠ f01 (Function.update y i (!y i)) := by
  fin_cases i
  · exact ⟨![false, true, false, false, false, true, false], by decide⟩
  · exact ⟨![false, false, false, false, false, false, true], by decide⟩
  · exact ⟨![true, false, false, false, true, false, false], by decide⟩
  · exact ⟨![false, false, false, false, true, false, false], by decide⟩
  · exact ⟨![false, false, false, true, false, false, false], by decide⟩
  · exact ⟨![true, true, false, false, false, false, false], by decide⟩
  · exact ⟨![false, true, false, false, false, false, false], by decide⟩

def stepReach (D : Circuit) (u v : ℕ) : Prop :=
  ∃ j : Fin D.gates.length, v = 7 + j.val ∧ u ∈ (D.gates.get j).inputs

def Reach (D : Circuit) (u v : ℕ) : Prop :=
  Relation.ReflTransGen (stepReach D) u v

lemma wval_eq_of_agree_on_reach {D : Circuit} (hws : WellStructured 7 D)
    {y1 y2 : Fin 7 → Bool} (v : ℕ) (hv : v < 7 + D.gates.length)
    (hagree : ∀ i : Fin 7, Reach D i.val v → y1 i = y2 i) :
    wval D y1 v = wval D y2 v := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    by_cases h7 : v < 7
    · rw [wval_input D y1 v h7, wval_input D y2 v h7]
      exact hagree ⟨v, h7⟩ Relation.ReflTransGen.refl
    · have hj : v - 7 < D.gates.length := by omega
      have hv' : v = 7 + (v - 7) := by omega
      rw [hv', wval_gate D y1 (v - 7) hj (ws_back hws _ hj),
          wval_gate D y2 (v - 7) hj (ws_back hws _ hj)]
      congr 1
      apply List.map_congr_left
      intro a ha
      have halt : a < 7 + (v - 7) := ws_back hws (v - 7) hj a ha
      apply ih a (by omega) (by omega)
      intro i hi
      apply hagree i
      exact Relation.ReflTransGen.tail hi ⟨⟨v - 7, hj⟩, hv', by simpa using ha⟩

lemma no_circuit_f01_le5 (D : Circuit) (hws : WellStructured 7 D) (hsz : D.size ≤ 5)
    (hout_lt : D.output < 7 + D.gates.length)
    (heval : ∀ y : Fin 7 → Bool, wval D y D.output = f01 y) : False := by
  classical
  have hout_ge7 : 7 ≤ D.output := by
    by_contra hlt
    have hlt' : D.output < 7 := by omega
    have h0 : ∃ i : Fin 7, i.val ≠ D.output := by
      by_cases h0 : D.output = 0
      · exact ⟨1, by omega⟩
      · exact ⟨0, by omega⟩
    obtain ⟨i, hi⟩ := h0
    obtain ⟨y, hy⟩ := f01_essential i
    have h1 := heval y
    have h2 := heval (Function.update y i (!y i))
    rw [wval_input D y D.output hlt'] at h1
    rw [wval_input D _ D.output hlt'] at h2
    have hne : (⟨D.output, hlt'⟩ : Fin 7) ≠ i := fun h => hi (congrArg Fin.val h).symm
    rw [Function.update_of_ne hne] at h2
    exact hy (h1.symm.trans h2)
  let R : Finset (Fin D.gates.length) :=
    Finset.univ.filter (fun j => Reach D (7 + j.val) D.output)
  have hout_idx_lt : D.output - 7 < D.gates.length := by omega
  have hout_mem : D.output ∈ R.image (fun j : Fin D.gates.length => 7 + j.val) := by
    rw [Finset.mem_image]
    refine ⟨⟨D.output - 7, hout_idx_lt⟩, ?_, by dsimp only; omega⟩
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    have : 7 + (D.output - 7) = D.output := by omega
    rw [this]
    exact Relation.ReflTransGen.refl
  have hin_read : ∀ i : Fin 7, ∃ j ∈ R, i.val ∈ (D.gates.get j).inputs := by
    intro i
    have hreach : Reach D i.val D.output := by
      by_contra hnr
      obtain ⟨y, hy⟩ := f01_essential i
      have heq := wval_eq_of_agree_on_reach hws D.output hout_lt
        (y1 := y) (y2 := Function.update y i (!y i)) (fun k hk => by
          have hne : k ≠ i := fun h => hnr (h ▸ hk)
          exact (Function.update_of_ne hne _ _).symm)
      rw [heval, heval] at heq
      exact hy heq
    rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨w, hstep, htail⟩
    · have := i.isLt; omega
    · rcases hstep with ⟨j, rfl, hmem⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htail⟩, hmem⟩
  have hgate_read : ∀ j ∈ R, 7 + j.val ≠ D.output →
      ∃ k ∈ R, 7 + j.val ∈ (D.gates.get k).inputs := by
    intro j hj hne
    have hreach : Reach D (7 + j.val) D.output := (Finset.mem_filter.mp hj).2
    rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨w, hstep, htail⟩
    · exact (hne heq).elim
    · rcases hstep with ⟨k, rfl, hmem⟩
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htail⟩, hmem⟩
  let Wreq : Finset ℕ :=
    (Finset.range 7) ∪ ((R.image (fun j : Fin D.gates.length => 7 + j.val)).erase D.output)
  have hdisj_W : Disjoint (Finset.range 7)
      ((R.image (fun j : Fin D.gates.length => 7 + j.val)).erase D.output) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rw [Finset.mem_range] at hw1
    rw [Finset.mem_erase, Finset.mem_image] at hw2
    rcases hw2.2 with ⟨j, _, rfl⟩
    omega
  have hWreq_card : Wreq.card = R.card + 6 := by
    rw [Finset.card_union_of_disjoint hdisj_W, Finset.card_range,
        Finset.card_erase_of_mem hout_mem,
        Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]
    have hRpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨⟨D.output - 7, hout_idx_lt⟩, by
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      have : 7 + (D.output - 7) = D.output := by omega
      rw [this]; exact Relation.ReflTransGen.refl⟩
    omega
  let insFin (j : Fin D.gates.length) : Finset ℕ := (D.gates.get j).inputs.toFinset
  have hsub : Wreq ⊆ R.biUnion insFin := by
    intro w hw
    rw [Finset.mem_biUnion]
    simp only [Wreq, Finset.mem_union, Finset.mem_range, Finset.mem_erase, Finset.mem_image] at hw
    rcases hw with hw7 | ⟨hne, ⟨j, hjR, rfl⟩⟩
    · obtain ⟨k, hkR, hmem⟩ := hin_read ⟨w, hw7⟩
      exact ⟨k, hkR, List.mem_toFinset.mpr hmem⟩
    · obtain ⟨k, hkR, hmem⟩ := hgate_read j hjR hne
      exact ⟨k, hkR, List.mem_toFinset.mpr hmem⟩
  have hlen_le2 : ∀ j ∈ R, (D.gates.get j).inputs.length ≤ 2 := by
    intro j _
    rcases hws j with ⟨_, _, _, hins⟩ | ⟨_, _, _, _, _, hins⟩
    · rw [hins]; simp
    · rw [hins]; simp
  have hR_le5 : R.card ≤ 5 := by
    calc R.card ≤ (Finset.univ : Finset (Fin D.gates.length)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = D.gates.length := by simp
      _ ≤ 5 := hsz
  have hsum_le : R.sum (fun j => (insFin j).card) ≤ 2 * R.card := by
    calc R.sum (fun j => (insFin j).card)
        ≤ R.sum (fun j => (D.gates.get j).inputs.length) :=
          Finset.sum_le_sum (fun j _ => List.toFinset_card_le _)
      _ ≤ R.sum (fun _ => 2) := Finset.sum_le_sum hlen_le2
      _ = 2 * R.card := by simp [Nat.mul_comm]
  have hcard_chain : R.card + 6 ≤ (R.biUnion insFin).card := by
    rw [← hWreq_card]; exact Finset.card_le_card hsub
  have hbi_le : (R.biUnion insFin).card ≤ R.sum (fun j => (insFin j).card) := Finset.card_biUnion_le
  omega

lemma reduce_prefix (gs : List Gate)
    (hws : ∀ j : Fin gs.length,
      ((gs.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧ (gs.get j).inputs = [a]) ∨
      (((gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
        ∃ a b, a < b ∧ b < 9 + j.val ∧ (gs.get j).inputs = [a, b]))
    (h0 : gs.head? = some ⟨GateOp.and, [0, 4]⟩)
    (h1 : gs.tail.head? = some ⟨GateOp.or, [1, 3]⟩) :
    let wC (y : Fin 7 → Bool) (w : ℕ) : Bool := (W gs (List.ofFn (ext2 y))).getD w false
    let isConst (w : ℕ) : Prop := ∃ b : Bool, ∀ y : Fin 7 → Bool, wC y w = b
    let S (j : Fin gs.length) : Prop :=
      2 ≤ j.val ∧ (isConst (9 + j.val) ∨ ∃ a ∈ (gs.get j).inputs, isConst a)
    ∃ (ds : List Gate) (mp : ℕ → ℕ),
      WellStructured 7 ⟨ds, 0⟩ ∧
      ds.length = (Finset.univ.filter (fun j : Fin gs.length => 2 ≤ j.val ∧ ¬ S j)).card ∧
      (∀ w < 9 + gs.length, ¬ isConst w → mp w < 7 + ds.length ∧
        ∀ y : Fin 7 → Bool, (W ds (List.ofFn y)).getD (mp w) false = wC y w) := by
  classical
  have hprefix : ∀ (k : ℕ) (hk : k ≤ gs.length),
      let wC (y : Fin 7 → Bool) (w : ℕ) : Bool := (W gs (List.ofFn (ext2 y))).getD w false
      let isConst (w : ℕ) : Prop := ∃ b : Bool, ∀ y : Fin 7 → Bool, wC y w = b
      let S (j : Fin gs.length) : Prop :=
        2 ≤ j.val ∧ (isConst (9 + j.val) ∨ ∃ a ∈ (gs.get j).inputs, isConst a)
      ∃ (ds : List Gate) (mp : ℕ → ℕ),
        WellStructured 7 ⟨ds, 0⟩ ∧
        ds.length = (Finset.univ.filter (fun j : Fin gs.length => j.val < k ∧ 2 ≤ j.val ∧ ¬ S j)).card ∧
        (∀ w < 9 + k, ¬ isConst w → mp w < 7 + ds.length ∧
          ∀ y : Fin 7 → Bool, (W ds (List.ofFn y)).getD (mp w) false = wC y w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => w - 2, ?_, by simp, ?_⟩
      · intro j; exact Fin.elim0 j
      · intro w hw hnc
        dsimp only at hw hnc ⊢
        have hwne0 : w ≠ 0 := by
          intro h0'
          apply hnc
          refine ⟨false, fun y => ?_⟩
          rw [h0', W_prefix gs (List.ofFn (ext2 y)) 0 (by simp)]
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
          rfl
        have hwne1 : w ≠ 1 := by
          intro h1'
          apply hnc
          refine ⟨true, fun y => ?_⟩
          rw [h1', W_prefix gs (List.ofFn (ext2 y)) 1 (by simp)]
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
          rfl
        refine ⟨by simp; omega, fun y => ?_⟩
        rw [W_prefix [] (List.ofFn y) (w - 2) (by simp; omega),
            W_prefix gs (List.ofFn (ext2 y)) w (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn,
            List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        match w with
        | 0 => omega
        | 1 => omega
        | w' + 2 =>
          have hsucc1 : (⟨w' + 2, by omega⟩ : Fin 9) = Fin.succ ⟨w' + 1, by omega⟩ := rfl
          have hsucc2 : (⟨w' + 1, by omega⟩ : Fin 8) = Fin.succ ⟨w', by omega⟩ := rfl
          simp only [Nat.add_sub_cancel, ext2, hsucc1, Fin.cons_succ, hsucc2]
    | succ k ih =>
      intro hk
      obtain ⟨ds, mp, hds_ws, hds_len, hmp⟩ := ih (by omega)
      let j : Fin gs.length := ⟨k, hk⟩
      have hjv : j.val = k := rfl
      have hgate_eval : ∀ y : Fin 7 → Bool,
          (W gs (List.ofFn (ext2 y))).getD (9 + k) false =
            (gs.get j).op.eval ((gs.get j).inputs.map fun a => (W gs (List.ofFn (ext2 y))).getD a false) := by
        intro y
        have hg := W_gate gs (List.ofFn (ext2 y)) k hk
        rw [List.length_ofFn] at hg
        rw [hg]
        simp only [List.get_eq_getElem, hjv]
        congr 1
        apply List.map_congr_left
        intro a ha
        rcases hws j with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
        · simp only [List.get_eq_getElem, hjv] at hins hu
          rw [hins, List.mem_singleton] at ha
          rw [if_pos (by omega)]
        · simp only [List.get_eq_getElem, hjv] at hins hu hv
          rw [hins, List.mem_cons, List.mem_singleton] at ha
          rcases ha with rfl | rfl <;> rw [if_pos (by omega)]
      by_cases hk2 : k < 2
      · have hconst_k : ∃ b : Bool, ∀ y : Fin 7 → Bool, (W gs (List.ofFn (ext2 y))).getD (9 + k) false = b := by
          have hk01 : k = 0 ∨ k = 1 := by omega
          rcases hk01 with hk0 | hk1
          · refine ⟨false, fun y => ?_⟩
            rw [hgate_eval y]
            have h0val : (W gs (List.ofFn (ext2 y))).getD 0 false = false := by
              rw [W_prefix gs (List.ofFn (ext2 y)) 0 (by simp)]
              rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
            have hg0 : gs.get j = ⟨GateOp.and, [0, 4]⟩ := by
              simp only [List.get_eq_getElem, hjv, hk0]
              exact getElem_zero_of_head? h0 (by omega)
            rw [hg0]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, h0val, Bool.false_and]
          · refine ⟨true, fun y => ?_⟩
            rw [hgate_eval y]
            have h1val : (W gs (List.ofFn (ext2 y))).getD 1 false = true := by
              rw [W_prefix gs (List.ofFn (ext2 y)) 1 (by simp)]
              rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
            have hg1 : gs.get j = ⟨GateOp.or, [1, 3]⟩ := by
              simp only [List.get_eq_getElem, hjv, hk1]
              exact getElem_one_of_tail_head? h1 (by omega)
            rw [hg1]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, h1val, Bool.true_or]
        refine ⟨ds, mp, hds_ws, ?_, ?_⟩
        · rw [hds_len]
          congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor <;> intro ⟨h1', h2', h3'⟩ <;> exact ⟨by omega, h2', h3'⟩
        · intro w hw hnc
          have hlt : w < 9 + k := by
            by_cases heq : w = 9 + k
            · subst heq; exact (hnc hconst_k).elim
            · omega
          exact hmp w hlt hnc
      · have hk2' : 2 ≤ k := by omega
        by_cases hS : (∃ b : Bool, ∀ y : Fin 7 → Bool, (W gs (List.ofFn (ext2 y))).getD (9 + k) false = b) ∨
            (∃ a ∈ (gs.get j).inputs, ∃ b : Bool, ∀ y : Fin 7 → Bool, (W gs (List.ofFn (ext2 y))).getD a false = b)
        · have hfilter_eq : (Finset.univ.filter (fun i : Fin gs.length => i.val < k + 1 ∧ 2 ≤ i.val ∧
              ¬ (2 ≤ i.val ∧ ((∃ b, ∀ y, (W gs (List.ofFn (ext2 y))).getD (9 + i.val) false = b) ∨
                ∃ a ∈ (gs.get i).inputs, ∃ b, ∀ y, (W gs (List.ofFn (ext2 y))).getD a false = b)))).card =
              (Finset.univ.filter (fun i : Fin gs.length => i.val < k ∧ 2 ≤ i.val ∧
              ¬ (2 ≤ i.val ∧ ((∃ b, ∀ y, (W gs (List.ofFn (ext2 y))).getD (9 + i.val) false = b) ∨
                ∃ a ∈ (gs.get i).inputs, ∃ b, ∀ y, (W gs (List.ofFn (ext2 y))).getD a false = b)))).card := by
            congr 1; ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hlt, h2i, hni⟩
              refine ⟨?_, h2i, hni⟩
              by_contra hge
              have hieq : i = j := Fin.ext (by omega)
              subst hieq
              exact hni ⟨hk2', hS⟩
            · rintro ⟨hlt, h2i, hni⟩; exact ⟨by omega, h2i, hni⟩
          by_cases hck : ∃ b : Bool, ∀ y : Fin 7 → Bool, (W gs (List.ofFn (ext2 y))).getD (9 + k) false = b
          · refine ⟨ds, mp, hds_ws, hds_len.trans hfilter_eq.symm, ?_⟩
            intro w hw hnc
            have hlt : w < 9 + k := by
              by_cases heq : w = 9 + k
              · subst heq; exact (hnc hck).elim
              · omega
            exact hmp w hlt hnc
          · have hcopy : ∃ a < 9 + k, (¬ ∃ b : Bool, ∀ y : Fin 7 → Bool, (W gs (List.ofFn (ext2 y))).getD a false = b) ∧
                ∀ y : Fin 7 → Bool, (W gs (List.ofFn (ext2 y))).getD (9 + k) false = (W gs (List.ofFn (ext2 y))).getD a false := by
              rcases hws j with ⟨hop, a, ha, hins⟩ | ⟨hop, a, b, hab, hb, hins⟩
              · rw [hjv] at ha
                rcases hS with hc | ⟨u, hu, cu, hcu⟩
                · exact (hck hc).elim
                · rw [hins, List.mem_singleton] at hu; subst hu
                  exfalso; apply hck; refine ⟨!cu, fun y => ?_⟩
                  rw [hgate_eval y, hop, hins]
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, hcu y]
              · rw [hjv] at hb
                rcases hS with hc | ⟨u, hu, cu, hcu⟩
                · exact (hck hc).elim
                · rw [hins, List.mem_cons, List.mem_singleton] at hu
                  rcases hu with rfl | rfl
                  · by_cases hcb : ∃ cb : Bool, ∀ y : Fin 7 → Bool, (W gs (List.ofFn (ext2 y))).getD b false = cb
                    · obtain ⟨cb, hcb⟩ := hcb
                      exfalso; apply hck
                      refine ⟨(gs.get j).op.eval [cu, cb], fun y => ?_⟩
                      rw [hgate_eval y, hins]
                      simp only [List.map_cons, List.map_nil, hcu y, hcb y]
                    · refine ⟨b, hb, hcb, fun y => ?_⟩
                      rw [hgate_eval y, hins]
                      rcases hop with hop | hop
                      · rw [hop]; cases cu
                        · exfalso; apply hck; refine ⟨false, fun z => ?_⟩
                          rw [hgate_eval z, hop, hins]
                          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, hcu z, Bool.false_and]
                        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, hcu y, Bool.true_and, Bool.and_true]
                      · rw [hop]; cases cu
                        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hcu y, Bool.false_or, Bool.or_false]
                        · exfalso; apply hck; refine ⟨true, fun z => ?_⟩
                          rw [hgate_eval z, hop, hins]
                          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hcu z, Bool.true_or]
                  · by_cases hca : ∃ ca : Bool, ∀ y : Fin 7 → Bool, (W gs (List.ofFn (ext2 y))).getD a false = ca
                    · obtain ⟨ca, hca⟩ := hca
                      exfalso; apply hck
                      refine ⟨(gs.get j).op.eval [ca, cu], fun y => ?_⟩
                      rw [hgate_eval y, hins]
                      simp only [List.map_cons, List.map_nil, hca y, hcu y]
                    · refine ⟨a, by omega, hca, fun y => ?_⟩
                      rw [hgate_eval y, hins]
                      rcases hop with hop | hop
                      · rw [hop]; cases cu
                        · exfalso; apply hck; refine ⟨false, fun z => ?_⟩
                          rw [hgate_eval z, hop, hins]
                          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, hcu z, Bool.and_false, Bool.false_and]
                        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, hcu y, Bool.and_true]
                      · rw [hop]; cases cu
                        · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hcu y, Bool.or_false]
                        · exfalso; apply hck; refine ⟨true, fun z => ?_⟩
                          rw [hgate_eval z, hop, hins]
                          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hcu z, Bool.or_true, Bool.true_or]
            obtain ⟨a, halt, hnca, hceq⟩ := hcopy
            obtain ⟨hmpa_lt, hmpa_ev⟩ := hmp a halt hnca
            let mp' (w : ℕ) : ℕ := if w = 9 + k then mp a else mp w
            refine ⟨ds, mp', hds_ws, hds_len.trans hfilter_eq.symm, ?_⟩
            intro w hw hnc
            by_cases heq : w = 9 + k
            · subst heq
              refine ⟨by simpa [mp'] using hmpa_lt, fun y => ?_⟩
              simp only [mp', ite_true]
              exact (hmpa_ev y).trans (hceq y).symm
            · simp only [mp', if_neg heq]
              exact hmp w (by omega) hnc
        · let gNew : Gate := ⟨(gs.get j).op, (gs.get j).inputs.map mp⟩
          let ds' : List Gate := ds ++ [gNew]
          let mp' (w : ℕ) : ℕ := if w = 9 + k then 7 + ds.length else mp w
          have hno_in_const : ∀ u ∈ (gs.get j).inputs,
              ¬ ∃ b : Bool, ∀ y : Fin 7 → Bool, (W gs (List.ofFn (ext2 y))).getD u false = b :=
            fun u hu hcu => hS (Or.inr ⟨u, hu, hcu⟩)
          have hds'_ws : WellStructured 7 ⟨ds', 0⟩ := by
            intro idx
            by_cases hlt : idx.val < ds.length
            · have hget : ds'.get idx = ds.get ⟨idx.val, hlt⟩ := by
                simp only [ds', List.get_eq_getElem, List.getElem_append_left hlt]
              rw [hget]; exact hds_ws ⟨idx.val, hlt⟩
            · have heq : idx.val = ds.length := by
                have := idx.isLt; simp [ds'] at this; omega
              have hget : ds'.get idx = gNew := by
                simp only [ds', List.get_eq_getElem, heq, List.getElem_append_right le_rfl,
                  Nat.sub_self, List.getElem_singleton]
              rw [hget, heq]
              rcases hws j with ⟨hop, a, ha, hins⟩ | ⟨hop, a, b, hab, hb, hins⟩
              · rw [hjv] at ha
                left
                refine ⟨hop, mp a, (hmp a ha (hno_in_const a (by rw [hins]; simp))).1, ?_⟩
                dsimp only [gNew]; rw [hins]; rfl
              · rw [hjv] at hb
                right
                refine ⟨hop, mp a, mp b,
                  (hmp a (by omega) (hno_in_const a (by rw [hins]; simp))).1,
                  (hmp b hb (hno_in_const b (by rw [hins]; simp))).1, ?_⟩
                dsimp only [gNew]; rw [hins]; rfl
          have hds'_len : ds'.length = (Finset.univ.filter (fun i : Fin gs.length => i.val < k + 1 ∧ 2 ≤ i.val ∧
              ¬ (2 ≤ i.val ∧ ((∃ b, ∀ y, (W gs (List.ofFn (ext2 y))).getD (9 + i.val) false = b) ∨
                ∃ a ∈ (gs.get i).inputs, ∃ b, ∀ y, (W gs (List.ofFn (ext2 y))).getD a false = b)))).card := by
            have hset : Finset.univ.filter (fun i : Fin gs.length => i.val < k + 1 ∧ 2 ≤ i.val ∧
                ¬ (2 ≤ i.val ∧ ((∃ b, ∀ y, (W gs (List.ofFn (ext2 y))).getD (9 + i.val) false = b) ∨
                  ∃ a ∈ (gs.get i).inputs, ∃ b, ∀ y, (W gs (List.ofFn (ext2 y))).getD a false = b))) =
              insert j (Finset.univ.filter (fun i : Fin gs.length => i.val < k ∧ 2 ≤ i.val ∧
                ¬ (2 ≤ i.val ∧ ((∃ b, ∀ y, (W gs (List.ofFn (ext2 y))).getD (9 + i.val) false = b) ∨
                  ∃ a ∈ (gs.get i).inputs, ∃ b, ∀ y, (W gs (List.ofFn (ext2 y))).getD a false = b)))) := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              constructor
              · rintro ⟨hlt, h2i, hni⟩
                by_cases heq : i.val = k
                · exact Or.inl (Fin.ext heq)
                · exact Or.inr ⟨by omega, h2i, hni⟩
              · rintro (rfl | ⟨hlt, h2i, hni⟩)
                · exact ⟨by simp [j], hk2', fun h => hS h.2⟩
                · exact ⟨by omega, h2i, hni⟩
            have hjnot : j ∉ Finset.univ.filter (fun i : Fin gs.length => i.val < k ∧ 2 ≤ i.val ∧
                ¬ (2 ≤ i.val ∧ ((∃ b, ∀ y, (W gs (List.ofFn (ext2 y))).getD (9 + i.val) false = b) ∨
                  ∃ a ∈ (gs.get i).inputs, ∃ b, ∀ y, (W gs (List.ofFn (ext2 y))).getD a false = b))) := by
              simp [j]
            rw [hset, Finset.card_insert_of_notMem hjnot, ← hds_len]
            simp [ds']
          refine ⟨ds', mp', hds'_ws, hds'_len, ?_⟩
          intro w hw hnc
          by_cases heq : w = 9 + k
          · subst heq
            refine ⟨by simp [mp', ds'], fun y => ?_⟩
            simp only [mp', ite_true, ds']
            rw [W_snoc]
            have hlen : (W ds (List.ofFn y)).length = 7 + ds.length := by
              rw [W_len, List.length_ofFn]
            have hstep : (step (W ds (List.ofFn y)) gNew).getD (7 + ds.length) false =
                gNew.op.eval (gNew.inputs.map fun i => (W ds (List.ofFn y)).getD i false) := by
              unfold step; rw [← hlen, getD_append_len]
            rw [hstep, hgate_eval y]
            simp only [gNew, List.map_map]
            congr 1
            apply List.map_congr_left
            intro a ha
            have halt : a < 9 + k := by
              rcases hws j with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
              · rw [hjv] at hu; rw [hins, List.mem_singleton] at ha; omega
              · rw [hjv] at hv; rw [hins, List.mem_cons, List.mem_singleton] at ha
                rcases ha with rfl | rfl <;> omega
            exact (hmp a halt (hno_in_const a ha)).2 y
          · have hlt : w < 9 + k := by omega
            obtain ⟨hltm, hevm⟩ := hmp w hlt hnc
            refine ⟨by simp [mp', if_neg heq, ds']; omega, fun y => ?_⟩
            simp only [mp', if_neg heq, ds']
            rw [W_snoc]
            have hlen : (W ds (List.ofFn y)).length = 7 + ds.length := by
              rw [W_len, List.length_ofFn]
            have hstep : (step (W ds (List.ofFn y)) gNew).getD (mp w) false =
                (W ds (List.ofFn y)).getD (mp w) false := by
              unfold step; exact getD_append_lt _ _ _ (by omega)
            rw [hstep]
            exact hevm y
  obtain ⟨ds, mp, h1', h2', h3'⟩ := hprefix gs.length le_rfl
  refine ⟨ds, mp, h1', ?_, h3'⟩
  rw [h2']
  congr 1; ext j
  simp

end PEqualNP.Outside.L_meta_27319

theorem PEqualNP.Outside.L_meta_27319 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩)) := by
  classical
  open PEqualNP.Outside.L_meta_27319 in
  rintro ⟨C, _, hsz, heval, hout, hnf, _, hfanout, hhead0, hhead1⟩
  have hlen_ge2 : 2 ≤ C.gates.length := by
    cases h : C.gates with
    | nil => simp [h] at hhead0
    | cons a l =>
      cases l with
      | nil => simp [h] at hhead1
      | cons b l' => simp
  have hlen_ge3 : 3 ≤ C.gates.length := by
    by_contra hlt
    have hlen2 : C.gates.length = 2 := by omega
    have hout10 : C.output = 9 + 1 := by
      change C.output + 1 = 9 + C.gates.length at hout; omega
    let x0 : Fin 9 → Bool := ![false, true, false, false, false, false, false, false, false]
    have hev := heval x0
    change wval C x0 C.output = pm3 x0 at hev
    rw [hout10] at hev
    have hback1 : ∀ a ∈ (C.gates[1]'(by omega)).inputs, a < 9 + 1 := by
      intro a ha
      rw [getElem_one_of_tail_head? hhead1 (by omega)] at ha
      simp at ha; rcases ha with rfl | rfl <;> omega
    rw [wval_gate C x0 1 (by omega) hback1, getElem_one_of_tail_head? hhead1 (by omega)] at hev
    have h1x : wval C x0 1 = true := by rw [wval_input C x0 1 (by omega)]; rfl
    simp only [List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
      List.any_cons, List.any_nil, id_eq, h1x, Bool.true_or] at hev
    have hpm : pm3 x0 = false := by decide
    rw [hpm] at hev
    cases hev
  have h0read : ∃ j : Fin C.gates.length, 2 ≤ j.val ∧ 0 ∈ (C.gates.get j).inputs := by
    by_contra hnone
    have hnone' : ∀ j : Fin C.gates.length, 2 ≤ j.val → 0 ∉ (C.gates.get j).inputs :=
      fun j hj hmem => hnone ⟨j, hj, hmem⟩
    let xT : Fin 9 → Bool := ![true, false, false, false, false, true, false, true, false]
    let xF : Fin 9 → Bool := ![false, false, false, false, false, true, false, true, false]
    have hsame : ∀ w < 9 + C.gates.length, w ≠ 0 →
        wval C xT w = wval C xF w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hne0
        by_cases h9 : w < 9
        · rw [wval_input C xT w h9, wval_input C xF w h9]
          interval_cases w <;> simp_all [xT, xF]
        · have hjlt : w - 9 < C.gates.length := by omega
          have hw' : w = 9 + (w - 9) := by omega
          let j : Fin C.gates.length := ⟨w - 9, hjlt⟩
          have hjv : j.val = w - 9 := rfl
          have hback : ∀ a ∈ (C.gates[w - 9]).inputs, a < 9 + (w - 9) := by
            intro a ha
            rcases hnf j with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
            · simp only [List.get_eq_getElem, hjv] at hins hu; rw [hins, List.mem_singleton] at ha; omega
            · simp only [List.get_eq_getElem, hjv] at hins hu hv; rw [hins, List.mem_cons, List.mem_singleton] at ha
              rcases ha with rfl | rfl <;> omega
          by_cases h2 : w - 9 < 2
          · rw [hw', wval_gate C xT (w - 9) hjlt hback, wval_gate C xF (w - 9) hjlt hback]
            have h4T : wval C xT 4 = false := by rw [wval_input C xT 4 (by omega)]; rfl
            have h4F : wval C xF 4 = false := by rw [wval_input C xF 4 (by omega)]; rfl
            have h1T : wval C xT 1 = false := by rw [wval_input C xT 1 (by omega)]; rfl
            have h1F : wval C xF 1 = false := by rw [wval_input C xF 1 (by omega)]; rfl
            have h3T : wval C xT 3 = false := by rw [wval_input C xT 3 (by omega)]; rfl
            have h3F : wval C xF 3 = false := by rw [wval_input C xF 3 (by omega)]; rfl
            have hw01 : w - 9 = 0 ∨ w - 9 = 1 := by omega
            rcases hw01 with hw0 | hw1
            · simp only [hw0]
              rw [getElem_zero_of_head? hhead0 (by omega)]
              simp [PEqualNP.CircuitLowerBounds.GateOp.eval, h4T, h4F]
            · simp only [hw1]
              rw [getElem_one_of_tail_head? hhead1 (by omega)]
              simp [PEqualNP.CircuitLowerBounds.GateOp.eval, h1T, h1F, h3T, h3F]
          · rw [hw', wval_gate C xT (w - 9) hjlt hback, wval_gate C xF (w - 9) hjlt hback]
            congr 1
            apply List.map_congr_left
            intro a ha
            have ha_lt : a < 9 + (w - 9) := hback a ha
            have ha_ne0 : a ≠ 0 := by
              intro h0a; subst h0a
              exact hnone' j (by omega) (by simpa [j] using ha)
            exact ih a (by omega) (by omega) ha_ne0
    have hout_eq : C.eval (List.ofFn xT) = C.eval (List.ofFn xF) := by
      have hout_lt : C.output < 9 + C.gates.length := by
        change C.output + 1 = 9 + C.gates.length at hout; omega
      have hout_ne0 : C.output ≠ 0 := by
        change C.output + 1 = 9 + C.gates.length at hout; omega
      exact hsame C.output hout_lt hout_ne0
    rw [heval xT, heval xF] at hout_eq
    have hcontra : pm3 xT ≠ pm3 xF := by decide
    exact hcontra hout_eq
  have h1read : ∃ j : Fin C.gates.length, 2 ≤ j.val ∧ 1 ∈ (C.gates.get j).inputs := by
    by_contra hnone
    have hnone' : ∀ j : Fin C.gates.length, 2 ≤ j.val → 1 ∉ (C.gates.get j).inputs :=
      fun j hj hmem => hnone ⟨j, hj, hmem⟩
    let yT : Fin 9 → Bool := ![false, true, false, true, false, false, false, false, true]
    let yF : Fin 9 → Bool := ![false, false, false, true, false, false, false, false, true]
    have hsame : ∀ w < 9 + C.gates.length, w ≠ 1 →
        wval C yT w = wval C yF w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hne1
        by_cases h9 : w < 9
        · rw [wval_input C yT w h9, wval_input C yF w h9]
          interval_cases w <;> simp_all [yT, yF]
        · have hjlt : w - 9 < C.gates.length := by omega
          have hw' : w = 9 + (w - 9) := by omega
          let j : Fin C.gates.length := ⟨w - 9, hjlt⟩
          have hjv : j.val = w - 9 := rfl
          have hback : ∀ a ∈ (C.gates[w - 9]).inputs, a < 9 + (w - 9) := by
            intro a ha
            rcases hnf j with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
            · simp only [List.get_eq_getElem, hjv] at hins hu; rw [hins, List.mem_singleton] at ha; omega
            · simp only [List.get_eq_getElem, hjv] at hins hu hv; rw [hins, List.mem_cons, List.mem_singleton] at ha
              rcases ha with rfl | rfl <;> omega
          by_cases h2 : w - 9 < 2
          · rw [hw', wval_gate C yT (w - 9) hjlt hback, wval_gate C yF (w - 9) hjlt hback]
            have h0T : wval C yT 0 = false := by rw [wval_input C yT 0 (by omega)]; rfl
            have h0F : wval C yF 0 = false := by rw [wval_input C yF 0 (by omega)]; rfl
            have h3T : wval C yT 3 = true := by rw [wval_input C yT 3 (by omega)]; rfl
            have h3F : wval C yF 3 = true := by rw [wval_input C yF 3 (by omega)]; rfl
            have hw01 : w - 9 = 0 ∨ w - 9 = 1 := by omega
            rcases hw01 with hw0 | hw1
            · simp only [hw0]
              rw [getElem_zero_of_head? hhead0 (by omega)]
              simp [PEqualNP.CircuitLowerBounds.GateOp.eval, h0T, h0F]
            · simp only [hw1]
              rw [getElem_one_of_tail_head? hhead1 (by omega)]
              simp [PEqualNP.CircuitLowerBounds.GateOp.eval, h3T, h3F]
          · rw [hw', wval_gate C yT (w - 9) hjlt hback, wval_gate C yF (w - 9) hjlt hback]
            congr 1
            apply List.map_congr_left
            intro a ha
            have ha_lt : a < 9 + (w - 9) := hback a ha
            have ha_ne1 : a ≠ 1 := by
              intro h1a; subst h1a
              exact hnone' j (by omega) (by simpa [j] using ha)
            exact ih a (by omega) (by omega) ha_ne1
    have hout_eq : C.eval (List.ofFn yT) = C.eval (List.ofFn yF) := by
      have hout_lt : C.output < 9 + C.gates.length := by
        change C.output + 1 = 9 + C.gates.length at hout; omega
      have hout_ne1 : C.output ≠ 1 := by
        change C.output + 1 = 9 + C.gates.length at hout; omega
      exact hsame C.output hout_lt hout_ne1
    rw [heval yT, heval yF] at hout_eq
    have hcontra : pm3 yT ≠ pm3 yF := by decide
    exact hcontra hout_eq
  let wC (y : Fin 7 → Bool) (w : ℕ) : Bool := (W C.gates (List.ofFn (ext2 y))).getD w false
  let isConst (w : ℕ) : Prop := ∃ b : Bool, ∀ y : Fin 7 → Bool, wC y w = b
  have hout_nc : ¬ isConst C.output := by
    rintro ⟨b, hb⟩
    have h1 := hb (fun _ => false)
    have h2 := hb (fun _ => true)
    have hf1 : wC (fun _ => false) C.output = f01 (fun _ => false) := heval (ext2 (fun _ => false))
    have hf2 : wC (fun _ => true) C.output = f01 (fun _ => true) := heval (ext2 (fun _ => true))
    rw [hf1] at h1; rw [hf2] at h2
    have hne : f01 (fun _ => false) ≠ f01 (fun _ => true) := by decide
    exact hne (h1.trans h2.symm)
  have hconst0 : isConst 0 := ⟨false, fun y => by
    dsimp only [wC]
    rw [W_prefix C.gates (List.ofFn (ext2 y)) 0 (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl⟩
  have hconst1 : isConst 1 := ⟨true, fun y => by
    dsimp only [wC]
    rw [W_prefix C.gates (List.ofFn (ext2 y)) 1 (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl⟩
  have hconst9 : isConst 9 := ⟨false, fun y => by
    have h0v : wC y 0 = false := by
      dsimp only [wC]
      rw [W_prefix C.gates (List.ofFn (ext2 y)) 0 (by simp)]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
    have hg0 : C.gates[0]'(by omega) = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ :=
      getElem_zero_of_head? hhead0 (by omega)
    have h1 := wval_gate C (ext2 y) 0 (by omega) (by rw [hg0]; intro a ha; simp at ha; rcases ha with rfl | rfl <;> omega)
    rw [hg0] at h1
    change wC y 9 = _ at h1
    rw [h1]
    simp only [List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
      List.all_cons, List.all_nil, id_eq]
    change (wC y 0 && (wC y 4 && true)) = false
    rw [h0v]; rfl⟩
  have hconst10 : isConst 10 := ⟨true, fun y => by
    have h1v : wC y 1 = true := by
      dsimp only [wC]
      rw [W_prefix C.gates (List.ofFn (ext2 y)) 1 (by simp)]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
    have hg1 : C.gates[1]'(by omega) = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩ :=
      getElem_one_of_tail_head? hhead1 (by omega)
    have h1 := wval_gate C (ext2 y) 1 (by omega) (by rw [hg1]; intro a ha; simp at ha; rcases ha with rfl | rfl <;> omega)
    rw [hg1] at h1
    change wC y 10 = _ at h1
    rw [h1]
    simp only [List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
      List.any_cons, List.any_nil, id_eq]
    change (wC y 1 || (wC y 3 || false)) = true
    rw [h1v]; rfl⟩
  let CK : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j => 2 ≤ j.val ∧ isConst (9 + j.val))
  let S : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j => 2 ≤ j.val ∧ (isConst (9 + j.val) ∨ ∃ a ∈ (C.gates.get j).inputs, isConst a))
  have hCK_sub_S : CK ⊆ S := by
    intro j hj
    simp only [CK, S, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, Or.inl hj.2⟩
  let Kact : Finset ℕ := ({0, 1, 9, 10} : Finset ℕ) ∪ CK.image (fun j => 9 + j.val)
  have hKact_disj : Disjoint ({0, 1, 9, 10} : Finset ℕ) (CK.image (fun j => 9 + j.val)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw1
    rw [Finset.mem_image] at hw2
    rcases hw2 with ⟨j, hj, rfl⟩
    have hj2 : 2 ≤ j.val := (Finset.mem_filter.mp hj).2.1
    omega
  have hKact_card : Kact.card = 4 + CK.card := by
    rw [Finset.card_union_of_disjoint hKact_disj,
        Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]
    have h4 : ({0, 1, 9, 10} : Finset ℕ).card = 4 := by decide
    rw [h4]
  have hKact_const : ∀ w ∈ Kact, isConst w := by
    intro w hw
    simp only [Kact, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hw
    rcases hw with (rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩
    · exact hconst0
    · exact hconst1
    · exact hconst9
    · exact hconst10
    · exact (Finset.mem_filter.mp hj).2.2
  have hKact_sub : Kact ⊆ S.biUnion (fun j => (C.gates.get j).inputs.toFinset ∩ Kact) := by
    intro w hw
    rw [Finset.mem_biUnion]
    have hcw := hKact_const w hw
    simp only [Kact, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hw
    rcases hw with (rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩
    · obtain ⟨k, hk2, hmem⟩ := h0read
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk2, Or.inr ⟨0, hmem, hconst0⟩⟩, ?_⟩
      exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hmem, by simp [Kact]⟩
    · obtain ⟨k, hk2, hmem⟩ := h1read
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk2, Or.inr ⟨1, hmem, hconst1⟩⟩, ?_⟩
      exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hmem, by simp [Kact]⟩
    · obtain ⟨k, hkgt, hmem⟩ := hfanout ⟨0, by omega⟩ (by dsimp only; omega)
      have hk2 : 2 ≤ k.val := by
        by_contra hlt
        have hk1 : k.val = 1 := by simp at hkgt; omega
        have hg1 : C.gates.get k = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩ := by
          simp only [List.get_eq_getElem, hk1]
          exact getElem_one_of_tail_head? hhead1 (by omega)
        rw [hg1] at hmem; simp at hmem
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk2, Or.inr ⟨9, hmem, hconst9⟩⟩, ?_⟩
      exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hmem, by simp [Kact]⟩
    · obtain ⟨k, hkgt, hmem⟩ := hfanout ⟨1, by omega⟩ (by dsimp only; omega)
      have hk2 : 2 ≤ k.val := by simp at hkgt; omega
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk2, Or.inr ⟨10, hmem, hconst10⟩⟩, ?_⟩
      exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hmem, by simp [Kact]⟩
    · have hjlt : j.val + 1 < C.gates.length := by
        have hlt := j.isLt
        by_contra hge
        have heq : 9 + j.val = C.output := by
          change C.output + 1 = 9 + C.gates.length at hout; omega
        rw [heq] at hcw
        exact hout_nc hcw
      obtain ⟨k, hkgt, hmem⟩ := hfanout j hjlt
      have hk2 : 2 ≤ k.val := by
        have hj2 : 2 ≤ j.val := (Finset.mem_filter.mp hj).2.1
        omega
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk2, Or.inr ⟨9 + j.val, hmem, hcw⟩⟩, ?_⟩
      refine Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hmem, ?_⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hslot_bound : ∀ j ∈ S, ((C.gates.get j).inputs.toFinset ∩ Kact).card ≤ if j ∈ CK then 2 else 1 := by
    intro j hj
    by_cases hjCK : j ∈ CK
    · rw [if_pos hjCK]
      have hle : ((C.gates.get j).inputs.toFinset ∩ Kact).card ≤ (C.gates.get j).inputs.length :=
        (Finset.card_le_card Finset.inter_subset_left).trans (List.toFinset_card_le _)
      have hlen2 : (C.gates.get j).inputs.length ≤ 2 := by
        rcases hnf j with ⟨_, _, _, hins⟩ | ⟨_, _, _, _, _, hins⟩ <;> rw [hins] <;> simp
      exact hle.trans hlen2
    · rw [if_neg hjCK]
      have hj2 : 2 ≤ j.val := (Finset.mem_filter.mp hj).2.1
      have hjnc : ¬ isConst (9 + j.val) := fun hc =>
        hjCK (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj2, hc⟩)
      have hgate_ev : ∀ y : Fin 7 → Bool,
          wC y (9 + j.val) = (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun a => wC y a) := by
        intro y
        have h1 := wval_gate C (ext2 y) j.val j.isLt (by
          intro a ha
          rcases hnf j with ⟨_, u, hu, hins⟩ | ⟨_, u, v, hu, hv, hins⟩
          · simp only [List.get_eq_getElem] at hins hu; rw [hins, List.mem_singleton] at ha; omega
          · simp only [List.get_eq_getElem] at hins hu hv; rw [hins, List.mem_cons, List.mem_singleton] at ha
            rcases ha with rfl | rfl <;> omega)
        simpa [wC, wval, wires_eq_W] using h1
      rcases hnf j with ⟨hop, a, _, hins⟩ | ⟨hop, a, b, _, _, hins⟩
      · by_cases haK : a ∈ Kact
        · obtain ⟨ca, hca⟩ := hKact_const a haK
          exfalso; apply hjnc; refine ⟨!ca, fun y => ?_⟩
          rw [hgate_ev y, hop, hins]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval, hca y]
        · rw [hins]
          have hempty : ([a] : List ℕ).toFinset ∩ Kact = ∅ := by
            ext x; simp; rintro rfl; exact haK
          rw [hempty]; simp
      · by_cases haK : a ∈ Kact
        · by_cases hbK : b ∈ Kact
          · obtain ⟨ca, hca⟩ := hKact_const a haK
            obtain ⟨cb, hcb⟩ := hKact_const b hbK
            exfalso; apply hjnc; refine ⟨(C.gates.get j).op.eval [ca, cb], fun y => ?_⟩
            rw [hgate_ev y, hins]; simp [hca y, hcb y]
          · rw [hins]
            have hsub1 : ([a, b] : List ℕ).toFinset ∩ Kact ⊆ {a} := by
              intro x hx; simp at hx
              rcases hx.1 with rfl | rfl
              · simp
              · exact (hbK hx.2).elim
            exact (Finset.card_le_card hsub1).trans (by simp)
        · rw [hins]
          have hsub1 : ([a, b] : List ℕ).toFinset ∩ Kact ⊆ {b} := by
            intro x hx; simp at hx
            rcases hx.1 with rfl | rfl
            · exact (haK hx.2).elim
            · simp
          exact (Finset.card_le_card hsub1).trans (by simp)
  have hS_ge4 : 4 ≤ S.card := by
    have h1 : Kact.card ≤ S.sum (fun j => ((C.gates.get j).inputs.toFinset ∩ Kact).card) :=
      (Finset.card_le_card hKact_sub).trans Finset.card_biUnion_le
    have h2 : S.sum (fun j => ((C.gates.get j).inputs.toFinset ∩ Kact).card) ≤
        S.sum (fun j => if j ∈ CK then 2 else 1) := Finset.sum_le_sum hslot_bound
    have h3 : S.sum (fun j => if j ∈ CK then 2 else 1) = S.card + CK.card := by
      have hsplit : ∀ j : Fin C.gates.length, (if j ∈ CK then 2 else 1) = 1 + (if j ∈ CK then 1 else 0) := by
        intro j; split_ifs <;> rfl
      simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.sum_boole, Nat.cast_id]
      have : S.filter (fun j => j ∈ CK) = CK := by
        ext j; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hCK_sub_S h, h⟩⟩
      rw [this]
    omega
  obtain ⟨ds, mp, hds_ws, hds_len, hmp⟩ := reduce_prefix C.gates hnf hhead0 hhead1
  have hkeep_card : (Finset.univ.filter (fun j : Fin C.gates.length => 2 ≤ j.val ∧
      ¬ (2 ≤ j.val ∧ (isConst (9 + j.val) ∨ ∃ a ∈ (C.gates.get j).inputs, isConst a)))).card ≤ 5 := by
    let G2 : Finset (Fin C.gates.length) := Finset.univ.filter (fun j => 2 ≤ j.val)
    have hG2_card : G2.card = C.gates.length - 2 := by
      have hcomp : G2 = Finset.univ \ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin C.gates.length)) := by
        ext j; simp only [G2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h2 h; rcases h with rfl | rfl <;> simp at h2
        · intro h; by_contra hlt
          have hj01 : j.val = 0 ∨ j.val = 1 := by omega
          rcases hj01 with hv | hv
          · exact h (Or.inl (Fin.ext hv))
          · exact h (Or.inr (Fin.ext hv))
      rw [hcomp, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have hne01 : (⟨0, by omega⟩ : Fin C.gates.length) ≠ ⟨1, by omega⟩ := by simp
      rw [Finset.card_pair hne01]
    have hS_sub_G2 : S ⊆ G2 := fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
    have hdiff : Finset.univ.filter (fun j : Fin C.gates.length => 2 ≤ j.val ∧
        ¬ (2 ≤ j.val ∧ (isConst (9 + j.val) ∨ ∃ a ∈ (C.gates.get j).inputs, isConst a))) = G2 \ S := by
      ext j; simp only [G2, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    rw [hdiff, Finset.card_sdiff_of_subset hS_sub_G2, hG2_card]
    change C.gates.length ≤ 11 at hsz
    omega
  have hds_le5 : ds.length ≤ 5 := by
    have heq_len : ds.length = (Finset.univ.filter (fun j : Fin C.gates.length => 2 ≤ j.val ∧
        ¬ (2 ≤ j.val ∧ (isConst (9 + j.val) ∨ ∃ a ∈ (C.gates.get j).inputs, isConst a)))).card := hds_len
    omega
  have hout_ltC : C.output < 9 + C.gates.length := by
    change C.output + 1 = 9 + C.gates.length at hout; omega
  obtain ⟨hout_ltD, hout_ev⟩ := hmp C.output hout_ltC hout_nc
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨ds, mp C.output⟩
  exact no_circuit_f01_le5 D hds_ws hds_le5 hout_ltD (fun y => by
    have h1 := hout_ev y
    have h2 := heval (ext2 y)
    exact h1.trans h2)
