import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1288_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

local instance : DecidableEq GateOp := gateOpDecEq

lemma zero_lt_add_two (a b c : ℕ) : 0 < a + b + 2 + c := by omega

def evalGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq_evalGates (C : Circuit) (x : List Bool) :
    C.wires x = evalGates C.gates x := rfl

lemma evalGates_nil (w : List Bool) : evalGates [] w = w := rfl

lemma evalGates_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    evalGates (g :: gs) w =
      evalGates gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma evalGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalGates (gs1 ++ gs2) w = evalGates gs2 (evalGates gs1 w) :=
  List.foldl_append

lemma evalGates_length (gs : List Gate) (w : List Bool) :
    (evalGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalGates]
  | cons g gs ih =>
      simp only [evalGates_cons, ih, List.length_append, List.length_cons, List.length_nil]
      omega

lemma getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (h : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  have h1 : i < (l1 ++ l2).length := by simp; omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, List.getElem?_eq_getElem h1,
    List.getElem_append_left h]

lemma getD_append_right {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  by_cases h2 : i - l1.length < l2.length
  · have h1 : i < (l1 ++ l2).length := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
      List.getElem_append_right h]
  · have h1 : ¬ i < (l1 ++ l2).length := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h1),
      List.getElem?_eq_none (Nat.le_of_not_lt h2)]

lemma evalGates_getD_lt (gs : List Gate) (w : List Bool) (m : ℕ) (hm : m < w.length) :
    (evalGates gs w).getD m false = w.getD m false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      rw [evalGates_cons]
      have hm' : m < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
        simp; omega
      rw [ih _ hm', getD_append_left _ _ _ _ hm]

lemma evalGates_singleton_last (g : Gate) (w : List Bool) :
    (evalGates [g] w).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [evalGates_cons, evalGates_nil]
  rw [getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma list_any_congr {α : Type} (xs : List α) (f g : α → Bool) (h : ∀ x ∈ xs, f x = g x) :
    xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.any_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w1 w2 : List Bool) (hmono : ∀ m, w1.getD m false = true → w2.getD m false = true)
    (ins : List ℕ) :
    op.eval (ins.map fun i => w1.getD i false) = true →
    op.eval (ins.map fun i => w2.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro h i hi
    exact hmono i (h i hi)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨w2.getD i false, ⟨i, hi, rfl⟩, hmono i hb⟩

lemma evalGates_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hmono : ∀ m, w1.getD m false = true → w2.getD m false = true) :
    ∀ m, (evalGates gs w1).getD m false = true → (evalGates gs w2).getD m false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hmono
  | cons g gs ih =>
      simp only [evalGates_cons]
      have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g (by simp)
      have hgs' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
        fun g' hg' => hgs g' (by simp [hg'])
      apply ih hgs'
      · simp [hlen]
      · intro m hm
        by_cases hlt : m < w1.length
        · rw [getD_append_left _ _ _ _ hlt] at hm
          rw [getD_append_left _ _ _ _ (hlen ▸ hlt)]
          exact hmono m hm
        · have hge1 : w1.length ≤ m := Nat.le_of_not_lt hlt
          have hge2 : w2.length ≤ m := hlen ▸ hge1
          rw [getD_append_right _ _ _ _ hge1] at hm
          rw [getD_append_right _ _ _ _ hge2]
          rw [← hlen]
          cases hdiff : m - w1.length with
          | zero =>
              simp only [hdiff, List.getD_cons_zero] at hm ⊢
              exact gateOp_eval_mono g.op hg w1 w2 hmono g.inputs hm
          | succ k =>
              simp [hdiff] at hm

lemma fanInTwo_notCount_zero (C : Circuit) (hfit : FanInTwo C) (hnot : notCount C = 0) :
    ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  have h1 := (hfit g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  rcases h1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    unfold notCount at hnot
    have hmem : g ∈ C.gates.filter (fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) := by
      rw [List.mem_filter]
      exact ⟨hg, by simp [h]⟩
    have hpos : 0 < (C.gates.filter (fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _))).length :=
      List.length_pos_of_mem hmem
    omega

def ReadsBackFrom (m : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]'hj).inputs, i < m + j

lemma readsBack_iff (n : ℕ) (C : Circuit) : ReadsBack n C ↔ ReadsBackFrom n C.gates := by
  unfold ReadsBack ReadsBackFrom gateAt
  constructor
  · intro h j hj i hi
    have heq : C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]'hj := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact h j hj i (heq ▸ hi)
  · intro h j hj i hi
    have heq : C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]'hj := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact h j hj i (heq ▸ hi)

lemma readsBackFrom_nil (m : ℕ) : ReadsBackFrom m [] := by
  intro j hj; simp at hj

lemma readsBackFrom_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (hg : ∀ i ∈ g.inputs, i < m) (hgs : ReadsBackFrom (m + 1) gs) :
    ReadsBackFrom m (g :: gs) := by
  intro j hj i hi
  cases j with
  | zero =>
      simp only [List.getElem_cons_zero] at hi
      have := hg i hi
      omega
  | succ k =>
      simp only [List.getElem_cons_succ] at hi
      have hk : k < gs.length := by simp at hj; omega
      have := hgs k hk i hi
      omega

lemma readsBackFrom_append (m : ℕ) (gs1 gs2 : List Gate)
    (h1 : ReadsBackFrom m gs1) (h2 : ReadsBackFrom (m + gs1.length) gs2) :
    ReadsBackFrom m (gs1 ++ gs2) := by
  intro j hj i hi
  by_cases hlt : j < gs1.length
  · rw [List.getElem_append_left hlt] at hi
    exact h1 j hlt i hi
  · have hge : gs1.length ≤ j := Nat.le_of_not_lt hlt
    rw [List.getElem_append_right hge] at hi
    have hk : j - gs1.length < gs2.length := by simp at hj; omega
    have := h2 (j - gs1.length) hk i hi
    omega

lemma notCount_append (gs1 gs2 : List Gate) :
    notCount ⟨gs1 ++ gs2, 0⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append, List.length_append]

lemma notCount_cons (g : Gate) (gs : List Gate) :
    notCount ⟨g :: gs, 0⟩ = (if g.op = GateOp.not then 1 else 0) + notCount ⟨gs, 0⟩ := by
  by_cases h : g.op = GateOp.not
  · simp [notCount, h]; omega
  · simp [notCount, h]

lemma notCount_nil : notCount ⟨[], 0⟩ = 0 := rfl

def orChain (cur nextIdx : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], cur)
  | u :: us =>
      let g : Gate := ⟨GateOp.or, [cur, u]⟩
      let res := orChain nextIdx (nextIdx + 1) us
      (g :: res.1, res.2)

lemma orChain_length (cur nextIdx : ℕ) (us : List ℕ) :
    (orChain cur nextIdx us).1.length = us.length := by
  induction us generalizing cur nextIdx with
  | nil => rfl
  | cons u us ih => simp [orChain, ih]

lemma orChain_out_lt (cur nextIdx : ℕ) (us : List ℕ) (hcur : cur < nextIdx) :
    (orChain cur nextIdx us).2 < nextIdx + us.length := by
  induction us generalizing cur nextIdx with
  | nil => simp [orChain]; exact hcur
  | cons u us ih =>
      simp only [orChain, List.length_cons]
      have := ih nextIdx (nextIdx + 1) (by omega)
      omega

lemma orChain_fanInTwo (cur nextIdx : ℕ) (us : List ℕ) :
    FanInTwo ⟨(orChain cur nextIdx us).1, 0⟩ := by
  induction us generalizing cur nextIdx with
  | nil => intro g hg; simp [orChain] at hg
  | cons u us ih =>
      intro g hg
      simp only [orChain, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨by simp, by simp⟩
      · exact ih nextIdx (nextIdx + 1) g hg

lemma orChain_notCount (cur nextIdx : ℕ) (us : List ℕ) :
    notCount ⟨(orChain cur nextIdx us).1, 0⟩ = 0 := by
  induction us generalizing cur nextIdx with
  | nil => rfl
  | cons u us ih =>
      simp only [orChain]
      rw [notCount_cons]
      simp [ih]

lemma orChain_readsBackFrom (cur nextIdx : ℕ) (us : List ℕ)
    (hcur : cur < nextIdx) (hus : ∀ u ∈ us, u < nextIdx) :
    ReadsBackFrom nextIdx (orChain cur nextIdx us).1 := by
  induction us generalizing cur nextIdx with
  | nil => exact readsBackFrom_nil _
  | cons u us ih =>
      simp only [orChain]
      apply readsBackFrom_cons
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hcur
        · exact hus i (by simp)
      · exact ih nextIdx (nextIdx + 1) (by omega)
          (fun v hv => Nat.lt_trans (hus v (by simp [hv])) (by omega))

lemma orChain_eval (cur : ℕ) (us : List ℕ) (w : List Bool)
    (hcur : cur < w.length) (hus : ∀ u ∈ us, u < w.length) :
    (evalGates (orChain cur w.length us).1 w).getD (orChain cur w.length us).2 false =
      (w.getD cur false || us.any (fun u => w.getD u false)) := by
  induction us generalizing cur w with
  | nil => simp [orChain, evalGates]
  | cons u us ih =>
      simp only [orChain, evalGates_cons, List.any_cons]
      set b : Bool := GateOp.or.eval ([cur, u].map fun i => w.getD i false)
      have hb : b = (w.getD cur false || w.getD u false) := by
        simp [b, GateOp.eval]
      set w' : List Bool := w ++ [b]
      have hw'len : w'.length = w.length + 1 := by simp [w']
      have h1 : w.length < w'.length := by omega
      have h2 : ∀ v ∈ us, v < w'.length :=
        fun v hv => Nat.lt_trans (hus v (by simp [hv])) (by omega)
      have hih := ih w.length w' h1 h2
      rw [hw'len] at hih
      rw [hih]
      have hw'last : w'.getD w.length false = b := by
        simp [w']
      have hany : us.any (fun v => w'.getD v false) = us.any (fun v => w.getD v false) := by
        apply list_any_congr
        intro v hv
        exact getD_append_left w [b] v false (hus v (by simp [hv]))
      rw [hw'last, hb, hany, Bool.or_assoc]

lemma fin3_eq (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  rcases k with ⟨v, hv⟩
  match v, hv with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr (Or.inl rfl)
  | 2, _ => exact Or.inr (Or.inr rfl)

lemma filter_fin3_eq_sum {α : Type} (xs : List α) (f : α → Fin 3) :
    (xs.filter (fun x => decide (f x = 0))).length +
    (xs.filter (fun x => decide (f x = 1))).length +
    (xs.filter (fun x => decide (f x = 2))).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.filter_cons, List.length_cons]
      rcases fin3_eq (f x) with h | h | h
      · rw [h]; simp only [decide_true,
          show decide ((0 : Fin 3) = 1) = false from rfl,
          show decide ((0 : Fin 3) = 2) = false from rfl,
          Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      · rw [h]; simp only [show decide ((1 : Fin 3) = 0) = false from rfl,
          decide_true,
          show decide ((1 : Fin 3) = 2) = false from rfl,
          Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      · rw [h]; simp only [show decide ((2 : Fin 3) = 0) = false from rfl,
          show decide ((2 : Fin 3) = 1) = false from rfl,
          decide_true,
          Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega

lemma filter_fin3_ne_sum {α : Type} (xs : List α) (f : α → Fin 3) :
    (xs.filter (fun x => decide (f x ≠ 0))).length +
    (xs.filter (fun x => decide (f x ≠ 1))).length +
    (xs.filter (fun x => decide (f x ≠ 2))).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.filter_cons, List.length_cons]
      rcases fin3_eq (f x) with h | h | h
      · rw [h]; simp only [show decide ((0 : Fin 3) ≠ 0) = false from rfl,
          show decide ((0 : Fin 3) ≠ 1) = true from rfl,
          show decide ((0 : Fin 3) ≠ 2) = true from rfl,
          Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      · rw [h]; simp only [show decide ((1 : Fin 3) ≠ 0) = true from rfl,
          show decide ((1 : Fin 3) ≠ 1) = false from rfl,
          show decide ((1 : Fin 3) ≠ 2) = true from rfl,
          Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      · rw [h]; simp only [show decide ((2 : Fin 3) ≠ 0) = true from rfl,
          show decide ((2 : Fin 3) ≠ 1) = true from rfl,
          show decide ((2 : Fin 3) ≠ 2) = false from rfl,
          Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega

def leftWires {l : ℕ} (a : Fin l → Fin 3) (k : Fin 3) : List ℕ :=
  ((List.finRange l).filter (fun i => decide (a i = k))).map Fin.val

def rightWires (l : ℕ) {r : ℕ} (c : Fin r → Fin 3) (k : Fin 3) : List ℕ :=
  ((List.finRange r).filter (fun j => decide (c j ≠ k))).map (fun j => l + j.val)

def allRightWires (l r : ℕ) : List ℕ :=
  (List.finRange r).map (fun j => l + j.val)

lemma leftWires_lt {l r : ℕ} (a : Fin l → Fin 3) (k : Fin 3) :
    ∀ u ∈ leftWires a k, u < l + r + 2 := by
  intro u hu
  simp only [leftWires, List.mem_map, List.mem_filter] at hu
  rcases hu with ⟨i, _, rfl⟩
  omega

lemma rightWires_lt {l r : ℕ} (c : Fin r → Fin 3) (k : Fin 3) :
    ∀ u ∈ rightWires l c k, u < l + r + 2 := by
  intro u hu
  simp only [rightWires, List.mem_map, List.mem_filter] at hu
  rcases hu with ⟨j, _, rfl⟩
  omega

lemma allRightWires_lt (l r : ℕ) :
    ∀ u ∈ allRightWires l r, u < l + r + 2 := by
  intro u hu
  simp only [allRightWires, List.mem_map] at hu
  rcases hu with ⟨j, _, rfl⟩
  omega

lemma leftWires_sum_len {l : ℕ} (a : Fin l → Fin 3) :
    (leftWires a 0).length + (leftWires a 1).length + (leftWires a 2).length = l := by
  simp only [leftWires, List.length_map]
  rw [filter_fin3_eq_sum, List.length_finRange]

lemma rightWires_sum_len (l : ℕ) {r : ℕ} (c : Fin r → Fin 3) :
    (rightWires l c 0).length + (rightWires l c 1).length + (rightWires l c 2).length = 2 * r := by
  simp only [rightWires, List.length_map]
  rw [filter_fin3_ne_sum, List.length_finRange]

lemma allRightWires_len (l r : ℕ) : (allRightWires l r).length = r := by
  simp [allRightWires]

lemma decC_iff (P : Prop) : @decide P (Classical.propDecidable P) = true ↔ P :=
  Iff.of_eq (@decide_eq_true_eq P (Classical.propDecidable P))

noncomputable def leftVec {l : ℕ} (r : ℕ) (i : Fin l) : List Bool :=
  (List.ofFn (fun h : Fin l => @decide (h = i) (Classical.propDecidable _)) ++
    List.replicate r false) ++ [false, true]

noncomputable def rightVec {l r : ℕ} (edge : Fin l → Fin r → Prop) (j : Fin r) : List Bool :=
  (List.ofFn (fun h : Fin l => @decide (edge h j) (Classical.propDecidable _)) ++
    List.ofFn (fun h : Fin r => @decide (h = j) (Classical.propDecidable _))) ++ [false, true]

lemma leftVec_len {l : ℕ} (r : ℕ) (i : Fin l) : (leftVec r i).length = l + r + 2 := by
  simp only [leftVec, List.length_append, List.length_ofFn, List.length_replicate,
    List.length_cons, List.length_nil]

lemma rightVec_len {l r : ℕ} (edge : Fin l → Fin r → Prop) (j : Fin r) :
    (rightVec edge j).length = l + r + 2 := by
  simp only [rightVec, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]

lemma leftVec_getD_left {l : ℕ} (r : ℕ) (i h : Fin l) :
    (leftVec r i).getD h.val false = @decide (h = i) (Classical.propDecidable _) := by
  unfold leftVec
  rw [getD_append_left _ _ _ _ (by simp; omega)]
  rw [getD_append_left _ _ _ _ (by simp)]
  have hlt : h.val < (List.ofFn (fun h' : Fin l => @decide (h' = i) (Classical.propDecidable _))).length := by
    simp
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]

lemma leftVec_getD_right {l r : ℕ} (i : Fin l) (j : Fin r) :
    (leftVec r i).getD (l + j.val) false = false := by
  unfold leftVec
  rw [getD_append_left _ _ _ _ (by simp)]
  rw [getD_append_right _ _ _ _ (by simp)]
  have hlt : l + j.val - (List.ofFn (fun h : Fin l => @decide (h = i) (Classical.propDecidable _))).length <
      (List.replicate r false).length := by
    simp
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_replicate]

lemma leftVec_getD_false {l : ℕ} (r : ℕ) (i : Fin l) :
    (leftVec r i).getD (l + r) false = false := by
  unfold leftVec
  rw [getD_append_right _ _ _ _ (by simp)]
  simp

lemma leftVec_getD_true {l : ℕ} (r : ℕ) (i : Fin l) :
    (leftVec r i).getD (l + r + 1) false = true := by
  unfold leftVec
  rw [getD_append_right _ _ _ _ (by simp)]
  have h : l + r + 1 - (l + r) = 1 := by omega
  simp [h]

lemma rightVec_getD_left {l r : ℕ} (edge : Fin l → Fin r → Prop) (j : Fin r) (h : Fin l) :
    (rightVec edge j).getD h.val false = @decide (edge h j) (Classical.propDecidable _) := by
  unfold rightVec
  rw [getD_append_left _ _ _ _ (by simp; omega)]
  rw [getD_append_left _ _ _ _ (by simp)]
  have hlt : h.val < (List.ofFn (fun h' : Fin l => @decide (edge h' j) (Classical.propDecidable _))).length := by
    simp
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]

lemma rightVec_getD_right {l r : ℕ} (edge : Fin l → Fin r → Prop) (j h : Fin r) :
    (rightVec edge j).getD (l + h.val) false = @decide (h = j) (Classical.propDecidable _) := by
  unfold rightVec
  rw [getD_append_left _ _ _ _ (by simp)]
  rw [getD_append_right _ _ _ _ (by simp)]
  have hlt : l + h.val - (List.ofFn (fun h' : Fin l => @decide (edge h' j) (Classical.propDecidable _))).length <
      (List.ofFn (fun h' : Fin r => @decide (h' = j) (Classical.propDecidable _))).length := by
    simp
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
  congr 1
  ext
  simp

lemma rightVec_getD_false {l r : ℕ} (edge : Fin l → Fin r → Prop) (j : Fin r) :
    (rightVec edge j).getD (l + r) false = false := by
  unfold rightVec
  rw [getD_append_right _ _ _ _ (by simp)]
  simp

lemma rightVec_getD_true {l r : ℕ} (edge : Fin l → Fin r → Prop) (j : Fin r) :
    (rightVec edge j).getD (l + r + 1) false = true := by
  unfold rightVec
  rw [getD_append_right _ _ _ _ (by simp)]
  have h : l + r + 1 - (l + r) = 1 := by omega
  simp [h]

lemma leftVec_le_rightVec {l r : ℕ} (edge : Fin l → Fin r → Prop)
    (i : Fin l) (j : Fin r) (hed : edge i j) :
    ∀ m, (leftVec r i).getD m false = true → (rightVec edge j).getD m false = true := by
  intro m hm
  by_cases h1 : m < l
  · let h : Fin l := ⟨m, h1⟩
    have := leftVec_getD_left r i h
    rw [this, decC_iff] at hm
    rw [rightVec_getD_left edge j h, hm, decC_iff]
    exact hed
  · by_cases h2 : m < l + r
    · let h : Fin r := ⟨m - l, by omega⟩
      have hm_eq : m = l + h.val := by simp [h]; omega
      rw [hm_eq, leftVec_getD_right] at hm
      cases hm
    · by_cases h3 : m = l + r
      · subst h3; rw [leftVec_getD_false] at hm; cases hm
      · by_cases h4 : m = l + r + 1
        · subst h4; exact rightVec_getD_true edge j
        · have hge : (leftVec r i).length ≤ m := by rw [leftVec_len]; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hm

lemma any_leftWires_leftVec {l : ℕ} (r : ℕ) (a : Fin l → Fin 3) (k : Fin 3) (i : Fin l) :
    (leftWires a k).any (fun u => (leftVec r i).getD u false) =
      @decide (k = a i) (Classical.propDecidable _) := by
  apply Bool.eq_iff_iff.mpr
  rw [decC_iff]
  simp only [leftWires, List.any_map, List.any_eq_true, List.mem_filter, List.mem_finRange,
    true_and, Function.comp_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hah, hval⟩
    rw [leftVec_getD_left, decC_iff] at hval
    subst hval; exact hah.symm
  · intro hk
    exact ⟨i, hk.symm, by rw [leftVec_getD_left, decC_iff]⟩

lemma any_rightWires_leftVec {l r : ℕ} (c : Fin r → Fin 3) (k : Fin 3) (i : Fin l) :
    (rightWires l c k).any (fun u => (leftVec r i).getD u false) = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [rightWires, List.any_map, List.any_eq_true, List.mem_filter,
    Function.comp_apply] at h
  rcases h with ⟨j, _, hval⟩
  rw [leftVec_getD_right] at hval
  cases hval

lemma any_rightWires_rightVec {l r : ℕ} (edge : Fin l → Fin r → Prop)
    (c : Fin r → Fin 3) (k : Fin 3) (j : Fin r) :
    (rightWires l c k).any (fun u => (rightVec edge j).getD u false) =
      @decide (k ≠ c j) (Classical.propDecidable _) := by
  apply Bool.eq_iff_iff.mpr
  rw [decC_iff]
  simp only [rightWires, List.any_map, List.any_eq_true, List.mem_filter, List.mem_finRange,
    true_and, Function.comp_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hch, hval⟩
    rw [rightVec_getD_right, decC_iff] at hval
    subst hval; exact Ne.symm hch
  · intro hk
    exact ⟨j, Ne.symm hk, by rw [rightVec_getD_right, decC_iff]⟩

lemma any_leftWires_rightVec_imp {l r : ℕ} (edge : Fin l → Fin r → Prop)
    (a : Fin l → Fin 3) (c : Fin r → Fin 3)
    (hcol : ∀ i j, edge i j → a i ≠ c j) (k : Fin 3) (j : Fin r) :
    (leftWires a k).any (fun u => (rightVec edge j).getD u false) = true → k ≠ c j := by
  simp only [leftWires, List.any_map, List.any_eq_true, List.mem_filter, List.mem_finRange,
    true_and, Function.comp_apply, decide_eq_true_eq]
  rintro ⟨i, hai, hval⟩
  rw [rightVec_getD_left, decC_iff] at hval
  rw [← hai]
  exact hcol i j hval

lemma any_allRightWires_leftVec {l : ℕ} (r : ℕ) (i : Fin l) :
    (allRightWires l r).any (fun u => (leftVec r i).getD u false) = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [allRightWires, List.any_map, List.any_eq_true, Function.comp_apply] at h
  rcases h with ⟨j, _, hval⟩
  rw [leftVec_getD_right] at hval
  cases hval

lemma any_allRightWires_rightVec {l r : ℕ} (edge : Fin l → Fin r → Prop) (j : Fin r) :
    (allRightWires l r).any (fun u => (rightVec edge j).getD u false) = true := by
  simp only [allRightWires, List.any_map, List.any_eq_true, List.mem_finRange,
    true_and, Function.comp_apply]
  exact ⟨j, by rw [rightVec_getD_right, decC_iff]⟩

def fin3Pick (x0 x1 x2 : ℕ) : Fin 3 → ℕ
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1
  | ⟨2, _⟩ => x2

lemma fin3Pick_0 (x0 x1 x2 : ℕ) : fin3Pick x0 x1 x2 0 = x0 := rfl
lemma fin3Pick_1 (x0 x1 x2 : ℕ) : fin3Pick x0 x1 x2 1 = x1 := rfl
lemma fin3Pick_2 (x0 x1 x2 : ℕ) : fin3Pick x0 x1 x2 2 = x2 := rfl

lemma fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ k : Fin 3, P k := by
  intro ⟨v, hv⟩
  match v, hv with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2

def buildMono (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3) :
    Circuit × (Fin 3 → ℕ) :=
  let n := l + r + 2
  let fw := l + r
  let s0 := leftWires a 0 ++ rightWires l c 0
  let s1 := leftWires a 1 ++ rightWires l c 1
  let s2 := leftWires a 2 ++ rightWires l c 2
  let r0 := orChain fw n s0
  let n1 := n + r0.1.length
  let r1 := orChain fw n1 s1
  let n2 := n1 + r1.1.length
  let r2 := orChain fw n2 s2
  let gs := r0.1 ++ r1.1 ++ r2.1
  (⟨gs, 0⟩, fin3Pick r0.2 r1.2 r2.2)

lemma buildMono_size (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3) :
    (buildMono l r a c).1.size = l + 2 * r := by
  unfold buildMono Circuit.size
  simp only [List.length_append, orChain_length]
  have hL := leftWires_sum_len a
  have hR := rightWires_sum_len l c
  omega

lemma buildMono_fanInTwo (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3) :
    FanInTwo (buildMono l r a c).1 := by
  unfold buildMono
  intro g hg
  simp only [List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact orChain_fanInTwo _ _ _ g hg
  · exact orChain_fanInTwo _ _ _ g hg
  · exact orChain_fanInTwo _ _ _ g hg

lemma buildMono_notCount (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3) :
    notCount (buildMono l r a c).1 = 0 := by
  unfold buildMono
  change notCount ⟨_ ++ _ ++ _, 0⟩ = 0
  rw [notCount_append, notCount_append, orChain_notCount, orChain_notCount, orChain_notCount]

lemma buildMono_readsBack (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3) :
    ReadsBack (l + r + 2) (buildMono l r a c).1 := by
  rw [readsBack_iff]
  unfold buildMono
  dsimp only
  have hs : ∀ k : Fin 3, ∀ u ∈ leftWires a k ++ rightWires l c k, u < l + r + 2 := by
    intro k u hu
    rw [List.mem_append] at hu
    rcases hu with hu | hu
    · exact leftWires_lt a k u hu
    · exact rightWires_lt c k u hu
  apply readsBackFrom_append
  · apply readsBackFrom_append
    · exact orChain_readsBackFrom _ _ _ (by omega) (hs 0)
    · exact orChain_readsBackFrom _ _ _ (by omega)
        (fun u hu => Nat.lt_of_lt_of_le (hs 1 u hu) (Nat.le_add_right _ _))
  · simp only [List.length_append]
    rw [← Nat.add_assoc]
    exact orChain_readsBackFrom _ _ _ (by omega)
      (fun u hu => Nat.lt_of_lt_of_le (hs 2 u hu) (by omega))

lemma buildMono_out_lt (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3) (k : Fin 3) :
    (buildMono l r a c).2 k < l + r + 2 + (buildMono l r a c).1.size := by
  unfold buildMono Circuit.size
  dsimp only
  set s0 := leftWires a 0 ++ rightWires l c 0
  set s1 := leftWires a 1 ++ rightWires l c 1
  set s2 := leftWires a 2 ++ rightWires l c 2
  set r0 := orChain (l + r) (l + r + 2) s0
  set r1 := orChain (l + r) (l + r + 2 + r0.1.length) s1
  set r2 := orChain (l + r) (l + r + 2 + r0.1.length + r1.1.length) s2
  have hl0 : r0.1.length = s0.length := orChain_length _ _ _
  have hl1 : r1.1.length = s1.length := orChain_length _ _ _
  have hl2 : r2.1.length = s2.length := orChain_length _ _ _
  have ho0 : r0.2 < l + r + 2 + s0.length := orChain_out_lt _ _ _ (by omega)
  have ho1 : r1.2 < l + r + 2 + r0.1.length + s1.length := orChain_out_lt _ _ _ (by omega)
  have ho2 : r2.2 < l + r + 2 + r0.1.length + r1.1.length + s2.length := orChain_out_lt _ _ _ (by omega)
  simp only [List.length_append]
  rcases fin3_eq k with rfl | rfl | rfl
  · rw [fin3Pick_0]; omega
  · rw [fin3Pick_1]; omega
  · rw [fin3Pick_2]; omega

lemma buildMono_eval (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3)
    (w : List Bool) (hwlen : w.length = l + r + 2) (hfw : w.getD (l + r) false = false)
    (k : Fin 3) :
    ((buildMono l r a c).1.wires w).getD ((buildMono l r a c).2 k) false =
      ((leftWires a k).any (fun u => w.getD u false) ||
       (rightWires l c k).any (fun u => w.getD u false)) := by
  have hs : ∀ k' : Fin 3, ∀ u ∈ leftWires a k' ++ rightWires l c k', u < l + r + 2 := by
    intro k' u hu
    rw [List.mem_append] at hu
    rcases hu with hu | hu
    · exact leftWires_lt a k' u hu
    · exact rightWires_lt c k' u hu
  unfold buildMono
  rw [wires_eq_evalGates]
  dsimp only
  set s0 := leftWires a 0 ++ rightWires l c 0
  set s1 := leftWires a 1 ++ rightWires l c 1
  set s2 := leftWires a 2 ++ rightWires l c 2
  set r0 := orChain (l + r) (l + r + 2) s0
  set r1 := orChain (l + r) (l + r + 2 + r0.1.length) s1
  set r2 := orChain (l + r) (l + r + 2 + r0.1.length + r1.1.length) s2
  rw [evalGates_append, evalGates_append]
  set w1 := evalGates r0.1 w
  set w2 := evalGates r1.1 w1
  have hw1len : w1.length = l + r + 2 + r0.1.length := by
    simp [w1, evalGates_length, hwlen]
  have hw2len : w2.length = l + r + 2 + r0.1.length + r1.1.length := by
    simp [w2, evalGates_length, hw1len, Nat.add_assoc]
  have hl0 : r0.1.length = s0.length := orChain_length _ _ _
  have hl1 : r1.1.length = s1.length := orChain_length _ _ _
  have hfw_n : l + r < l + r + 2 := by omega
  have hn_w1 : l + r + 2 ≤ w1.length := by rw [hw1len]; exact Nat.le_add_right _ _
  have hw1_w2 : w1.length ≤ w2.length := by rw [hw1len, hw2len]; exact Nat.le_add_right _ _
  rcases fin3_eq k with rfl | rfl | rfl
  · rw [fin3Pick_0]
    have ho0 : r0.2 < l + r + 2 + s0.length := orChain_out_lt _ _ _ hfw_n
    have hout0 : r0.2 < w1.length := by rw [hw1len, hl0]; exact ho0
    have hout0' : r0.2 < w2.length := Nat.lt_of_lt_of_le hout0 hw1_w2
    rw [evalGates_getD_lt _ _ _ hout0', evalGates_getD_lt _ _ _ hout0]
    have hev : (evalGates (orChain (l + r) w.length s0).1 w).getD
        (orChain (l + r) w.length s0).2 false =
        (w.getD (l + r) false || s0.any (fun u => w.getD u false)) :=
      orChain_eval (l + r) s0 w (hwlen ▸ hfw_n) (fun u hu => hwlen ▸ hs 0 u hu)
    rw [hwlen] at hev
    change (evalGates r0.1 w).getD r0.2 false = _
    rw [hev, hfw, Bool.false_or, List.any_append]
  · rw [fin3Pick_1]
    have hfw_w1 : l + r < w1.length := Nat.lt_of_lt_of_le hfw_n hn_w1
    have ho1 : r1.2 < l + r + 2 + r0.1.length + s1.length :=
      orChain_out_lt _ _ _ (hw1len ▸ hfw_w1)
    have hout1 : r1.2 < w2.length := by rw [hw2len, hl1]; exact ho1
    rw [evalGates_getD_lt _ _ _ hout1]
    have hev : (evalGates (orChain (l + r) w1.length s1).1 w1).getD
        (orChain (l + r) w1.length s1).2 false =
        (w1.getD (l + r) false || s1.any (fun u => w1.getD u false)) :=
      orChain_eval (l + r) s1 w1 hfw_w1 (fun u hu => Nat.lt_of_lt_of_le (hs 1 u hu) hn_w1)
    rw [hw1len] at hev
    change (evalGates r1.1 w1).getD r1.2 false = _
    rw [hev]
    have hfw1 : w1.getD (l + r) false = false := by
      rw [evalGates_getD_lt _ _ _ (hwlen ▸ hfw_n), hfw]
    have hany1 : s1.any (fun u => w1.getD u false) = s1.any (fun u => w.getD u false) := by
      apply list_any_congr
      intro u hu
      exact evalGates_getD_lt _ _ _ (hwlen ▸ hs 1 u hu)
    rw [hfw1, Bool.false_or, hany1, List.any_append]
  · rw [fin3Pick_2]
    have hfw_w1 : l + r < w1.length := Nat.lt_of_lt_of_le hfw_n hn_w1
    have hfw_w2 : l + r < w2.length := Nat.lt_of_lt_of_le hfw_w1 hw1_w2
    have hn_w2 : l + r + 2 ≤ w2.length := Nat.le_trans hn_w1 hw1_w2
    have hev : (evalGates (orChain (l + r) w2.length s2).1 w2).getD
        (orChain (l + r) w2.length s2).2 false =
        (w2.getD (l + r) false || s2.any (fun u => w2.getD u false)) :=
      orChain_eval (l + r) s2 w2 hfw_w2 (fun u hu => Nat.lt_of_lt_of_le (hs 2 u hu) hn_w2)
    rw [hw2len] at hev
    change (evalGates r2.1 w2).getD r2.2 false = _
    rw [hev]
    have hfw2 : w2.getD (l + r) false = false := by
      rw [evalGates_getD_lt _ _ _ hfw_w1, evalGates_getD_lt _ _ _ (hwlen ▸ hfw_n), hfw]
    have hany2 : s2.any (fun u => w2.getD u false) = s2.any (fun u => w.getD u false) := by
      apply list_any_congr
      intro u hu
      rw [evalGates_getD_lt _ _ _ (Nat.lt_of_lt_of_le (hs 2 u hu) hn_w1)]
      exact evalGates_getD_lt _ _ _ (hwlen ▸ hs 2 u hu)
    rw [hfw2, Bool.false_or, hany2, List.any_append]

def buildOneNotTap (l r : ℕ) (notAllR : ℕ) (lw rw : List ℕ) (nextIdx : ℕ) :
    List Gate × ℕ :=
  let fw := l + r
  let rL := orChain fw nextIdx lw
  let idxGL := nextIdx + rL.1.length
  let gGL : Gate := ⟨GateOp.and, [rL.2, notAllR]⟩
  let rR := orChain fw (idxGL + 1) rw
  let idxTap := idxGL + 1 + rR.1.length
  let gTap : Gate := ⟨GateOp.or, [idxGL, rR.2]⟩
  (rL.1 ++ [gGL] ++ rR.1 ++ [gTap], idxTap)

lemma buildOneNotTap_len (l r notAllR : ℕ) (lw rw : List ℕ) (nextIdx : ℕ) :
    (buildOneNotTap l r notAllR lw rw nextIdx).1.length = lw.length + rw.length + 2 := by
  unfold buildOneNotTap
  simp only [List.length_append, List.length_singleton, orChain_length]
  omega

lemma buildOneNotTap_out_lt (l r notAllR : ℕ) (lw rw : List ℕ) (nextIdx : ℕ) :
    (buildOneNotTap l r notAllR lw rw nextIdx).2 <
      nextIdx + (buildOneNotTap l r notAllR lw rw nextIdx).1.length := by
  rw [buildOneNotTap_len]
  unfold buildOneNotTap
  dsimp only
  rw [orChain_length, orChain_length]
  omega

lemma buildOneNotTap_fanInTwo (l r notAllR : ℕ) (lw rw : List ℕ) (nextIdx : ℕ) :
    FanInTwo ⟨(buildOneNotTap l r notAllR lw rw nextIdx).1, 0⟩ := by
  unfold buildOneNotTap
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with ((hg | rfl) | hg) | rfl
  · exact orChain_fanInTwo _ _ _ g hg
  · exact ⟨by simp, by simp⟩
  · exact orChain_fanInTwo _ _ _ g hg
  · exact ⟨by simp, by simp⟩

lemma buildOneNotTap_notCount (l r notAllR : ℕ) (lw rw : List ℕ) (nextIdx : ℕ) :
    notCount ⟨(buildOneNotTap l r notAllR lw rw nextIdx).1, 0⟩ = 0 := by
  unfold buildOneNotTap
  change notCount ⟨_ ++ [_] ++ _ ++ [_], 0⟩ = 0
  rw [notCount_append, notCount_append, notCount_append,
    orChain_notCount, orChain_notCount, notCount_cons, notCount_cons, notCount_nil]
  simp

lemma buildOneNotTap_readsBackFrom (l r notAllR : ℕ) (lw rw : List ℕ) (nextIdx : ℕ)
    (hfw : l + r < nextIdx) (hnot : notAllR < nextIdx)
    (hlw : ∀ u ∈ lw, u < nextIdx) (hrw : ∀ u ∈ rw, u < nextIdx) :
    ReadsBackFrom nextIdx (buildOneNotTap l r notAllR lw rw nextIdx).1 := by
  unfold buildOneNotTap
  dsimp only
  set rL := orChain (l + r) nextIdx lw
  set idxGL := nextIdx + rL.1.length
  set gGL : Gate := ⟨GateOp.and, [rL.2, notAllR]⟩
  set rR := orChain (l + r) (idxGL + 1) rw
  set gTap : Gate := ⟨GateOp.or, [idxGL, rR.2]⟩
  have hrL_len : rL.1.length = lw.length := orChain_length _ _ _
  have hrR_len : rR.1.length = rw.length := orChain_length _ _ _
  have hrL_out : rL.2 < idxGL := by
    have : rL.2 < nextIdx + lw.length := orChain_out_lt (l + r) nextIdx lw hfw
    omega
  have hrR_out : rR.2 < idxGL + 1 + rR.1.length := by
    have : rR.2 < idxGL + 1 + rw.length := orChain_out_lt (l + r) (idxGL + 1) rw (by omega)
    omega
  apply readsBackFrom_append
  · apply readsBackFrom_append
    · apply readsBackFrom_append
      · exact orChain_readsBackFrom (l + r) nextIdx lw hfw hlw
      · apply readsBackFrom_cons
        · intro i hi
          simp only [gGL, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
        · exact readsBackFrom_nil _
    · simp only [List.length_append, List.length_singleton]
      have heq : nextIdx + (rL.1.length + 1) = idxGL + 1 := by omega
      rw [heq]
      exact orChain_readsBackFrom (l + r) (idxGL + 1) rw (by omega)
        (fun u hu => Nat.lt_of_lt_of_le (hrw u hu) (by omega))
  · simp only [List.length_append, List.length_singleton]
    have heq : nextIdx + (rL.1.length + 1 + rR.1.length) = idxGL + 1 + rR.1.length := by omega
    rw [heq]
    apply readsBackFrom_cons
    · intro i hi
      simp only [gTap, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · exact readsBackFrom_nil _

lemma buildOneNotTap_eval (l r notAllR : ℕ) (lw rw : List ℕ) (w : List Bool)
    (hfw : l + r < w.length) (hfw0 : w.getD (l + r) false = false)
    (hnot : notAllR < w.length)
    (hlw : ∀ u ∈ lw, u < w.length) (hrw : ∀ u ∈ rw, u < w.length) :
    (evalGates (buildOneNotTap l r notAllR lw rw w.length).1 w).getD
      (buildOneNotTap l r notAllR lw rw w.length).2 false =
    ((lw.any (fun u => w.getD u false) && w.getD notAllR false) ||
     rw.any (fun u => w.getD u false)) := by
  unfold buildOneNotTap
  dsimp only
  set rL := orChain (l + r) w.length lw
  set idxGL := w.length + rL.1.length
  set gGL : Gate := ⟨GateOp.and, [rL.2, notAllR]⟩
  set rR := orChain (l + r) (idxGL + 1) rw
  set gTap : Gate := ⟨GateOp.or, [idxGL, rR.2]⟩
  rw [evalGates_append, evalGates_append, evalGates_append]
  set w1 := evalGates rL.1 w
  set w2 := evalGates [gGL] w1
  set w3 := evalGates rR.1 w2
  have hw1len : w1.length = idxGL := by simp [w1, idxGL, evalGates_length]
  have hw2len : w2.length = idxGL + 1 := by simp [w2, evalGates_length, hw1len]
  have hw3len : w3.length = idxGL + 1 + rR.1.length := by simp [w3, evalGates_length, hw2len]
  rw [← hw3len, evalGates_singleton_last]
  simp only [gTap, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    id_eq, Bool.or_false]
  have hw3_GL : w3.getD idxGL false = (lw.any (fun u => w.getD u false) && w.getD notAllR false) := by
    rw [evalGates_getD_lt _ _ _ (by omega)]
    rw [← hw1len, evalGates_singleton_last]
    simp only [gGL, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    have hLval : w1.getD rL.2 false = lw.any (fun u => w.getD u false) := by
      have := orChain_eval (l + r) lw w hfw hlw
      rw [this, hfw0, Bool.false_or]
    have hNval : w1.getD notAllR false = w.getD notAllR false :=
      evalGates_getD_lt _ _ _ hnot
    rw [hLval, hNval]
  have hw3_R : w3.getD rR.2 false = rw.any (fun u => w.getD u false) := by
    have hev := orChain_eval (l + r) rw w2 (by omega)
      (fun u hu => Nat.lt_of_lt_of_le (hrw u hu) (by omega))
    rw [hw2len] at hev
    change w3.getD rR.2 false = _
    rw [hev]
    have hfw2 : w2.getD (l + r) false = false := by
      rw [evalGates_getD_lt _ _ _ (by omega), evalGates_getD_lt _ _ _ hfw, hfw0]
    have hany : rw.any (fun u => w2.getD u false) = rw.any (fun u => w.getD u false) := by
      apply list_any_congr
      intro u hu
      rw [evalGates_getD_lt _ _ _ (by have := hrw u hu; omega)]
      exact evalGates_getD_lt _ _ _ (hrw u hu)
    rw [hfw2, Bool.false_or, hany]
  rw [hw3_GL, hw3_R]

def buildOneNot (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3) :
    Circuit × (Fin 3 → ℕ) :=
  let n := l + r + 2
  let fw := l + r
  let rAll := orChain fw n (allRightWires l r)
  let notIdx := n + rAll.1.length
  let gNot : Gate := ⟨GateOp.not, [rAll.2]⟩
  let n0 := notIdx + 1
  let t0 := buildOneNotTap l r notIdx (leftWires a 0) (rightWires l c 0) n0
  let n1 := n0 + t0.1.length
  let t1 := buildOneNotTap l r notIdx (leftWires a 1) (rightWires l c 1) n1
  let n2 := n1 + t1.1.length
  let t2 := buildOneNotTap l r notIdx (leftWires a 2) (rightWires l c 2) n2
  let gs := rAll.1 ++ [gNot] ++ t0.1 ++ t1.1 ++ t2.1
  (⟨gs, 0⟩, fin3Pick t0.2 t1.2 t2.2)

lemma buildOneNot_size (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3) :
    (buildOneNot l r a c).1.size = l + 3 * r + 7 := by
  unfold buildOneNot Circuit.size
  simp only [List.length_append, List.length_singleton, orChain_length,
    buildOneNotTap_len, allRightWires_len]
  have hL := leftWires_sum_len a
  have hR := rightWires_sum_len l c
  omega

lemma buildOneNot_fanInTwo (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3) :
    FanInTwo (buildOneNot l r a c).1 := by
  unfold buildOneNot
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with (((hg | rfl) | hg) | hg) | hg
  · exact orChain_fanInTwo _ _ _ g hg
  · exact ⟨by simp, by simp⟩
  · exact buildOneNotTap_fanInTwo _ _ _ _ _ _ g hg
  · exact buildOneNotTap_fanInTwo _ _ _ _ _ _ g hg
  · exact buildOneNotTap_fanInTwo _ _ _ _ _ _ g hg

lemma buildOneNot_notCount (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3) :
    notCount (buildOneNot l r a c).1 = 1 := by
  unfold buildOneNot
  change notCount ⟨_ ++ [_] ++ _ ++ _ ++ _, 0⟩ = 1
  rw [notCount_append, notCount_append, notCount_append, notCount_append,
    orChain_notCount, buildOneNotTap_notCount, buildOneNotTap_notCount, buildOneNotTap_notCount,
    notCount_cons, notCount_nil]
  simp

lemma buildOneNot_readsBack (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3) :
    ReadsBack (l + r + 2) (buildOneNot l r a c).1 := by
  rw [readsBack_iff]
  unfold buildOneNot
  dsimp only
  set n := l + r + 2
  set rAll := orChain (l + r) n (allRightWires l r)
  set notIdx := n + rAll.1.length
  set gNot : Gate := ⟨GateOp.not, [rAll.2]⟩
  set n0 := notIdx + 1
  set t0 := buildOneNotTap l r notIdx (leftWires a 0) (rightWires l c 0) n0
  set n1 := n0 + t0.1.length
  set t1 := buildOneNotTap l r notIdx (leftWires a 1) (rightWires l c 1) n1
  set n2 := n1 + t1.1.length
  set t2 := buildOneNotTap l r notIdx (leftWires a 2) (rightWires l c 2) n2
  have hrAll_len : rAll.1.length = (allRightWires l r).length := orChain_length _ _ _
  have hrAll_out : rAll.2 < notIdx := by
    have : rAll.2 < n + (allRightWires l r).length :=
      orChain_out_lt (l + r) n (allRightWires l r) (by omega)
    omega
  apply readsBackFrom_append
  · apply readsBackFrom_append
    · apply readsBackFrom_append
      · apply readsBackFrom_append
        · exact orChain_readsBackFrom (l + r) n (allRightWires l r) (by omega) (allRightWires_lt l r)
        · apply readsBackFrom_cons
          · intro i hi
            simp only [gNot, List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl
            exact hrAll_out
          · exact readsBackFrom_nil _
      · simp only [List.length_append, List.length_singleton]
        have heq : n + (rAll.1.length + 1) = n0 := by omega
        rw [heq]
        exact buildOneNotTap_readsBackFrom l r notIdx _ _ n0 (by omega) (by omega)
          (fun u hu => Nat.lt_of_lt_of_le (leftWires_lt (r := r) a 0 u hu) (by omega))
          (fun u hu => Nat.lt_of_lt_of_le (rightWires_lt c 0 u hu) (by omega))
    · simp only [List.length_append, List.length_singleton]
      have heq : n + (rAll.1.length + 1 + t0.1.length) = n1 := by omega
      rw [heq]
      exact buildOneNotTap_readsBackFrom l r notIdx _ _ n1 (by omega) (by omega)
        (fun u hu => Nat.lt_of_lt_of_le (leftWires_lt (r := r) a 1 u hu) (by omega))
        (fun u hu => Nat.lt_of_lt_of_le (rightWires_lt c 1 u hu) (by omega))
  · simp only [List.length_append, List.length_singleton]
    have heq : n + (rAll.1.length + 1 + t0.1.length + t1.1.length) = n2 := by omega
    rw [heq]
    exact buildOneNotTap_readsBackFrom l r notIdx _ _ n2 (by omega) (by omega)
      (fun u hu => Nat.lt_of_lt_of_le (leftWires_lt (r := r) a 2 u hu) (by omega))
      (fun u hu => Nat.lt_of_lt_of_le (rightWires_lt c 2 u hu) (by omega))

lemma buildOneNot_out_lt (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3) (k : Fin 3) :
    (buildOneNot l r a c).2 k < l + r + 2 + (buildOneNot l r a c).1.size := by
  unfold buildOneNot Circuit.size
  dsimp only
  set n := l + r + 2
  set rAll := orChain (l + r) n (allRightWires l r)
  set notIdx := n + rAll.1.length
  set n0 := notIdx + 1
  set t0 := buildOneNotTap l r notIdx (leftWires a 0) (rightWires l c 0) n0
  set n1 := n0 + t0.1.length
  set t1 := buildOneNotTap l r notIdx (leftWires a 1) (rightWires l c 1) n1
  set n2 := n1 + t1.1.length
  set t2 := buildOneNotTap l r notIdx (leftWires a 2) (rightWires l c 2) n2
  have ho0 : t0.2 < n0 + t0.1.length := buildOneNotTap_out_lt l r notIdx _ _ n0
  have ho1 : t1.2 < n1 + t1.1.length := buildOneNotTap_out_lt l r notIdx _ _ n1
  have ho2 : t2.2 < n2 + t2.1.length := buildOneNotTap_out_lt l r notIdx _ _ n2
  simp only [List.length_append, List.length_singleton]
  rcases fin3_eq k with rfl | rfl | rfl
  · rw [fin3Pick_0]; omega
  · rw [fin3Pick_1]; omega
  · rw [fin3Pick_2]; omega

lemma buildOneNot_eval (l r : ℕ) (a : Fin l → Fin 3) (c : Fin r → Fin 3)
    (w : List Bool) (hwlen : w.length = l + r + 2) (hfw : w.getD (l + r) false = false)
    (k : Fin 3) :
    ((buildOneNot l r a c).1.wires w).getD ((buildOneNot l r a c).2 k) false =
      (((leftWires a k).any (fun u => w.getD u false) &&
        !((allRightWires l r).any (fun u => w.getD u false))) ||
       (rightWires l c k).any (fun u => w.getD u false)) := by
  unfold buildOneNot
  rw [wires_eq_evalGates]
  dsimp only
  set n := l + r + 2
  set rAll := orChain (l + r) n (allRightWires l r)
  set notIdx := n + rAll.1.length
  set gNot : Gate := ⟨GateOp.not, [rAll.2]⟩
  set n0 := notIdx + 1
  set t0 := buildOneNotTap l r notIdx (leftWires a 0) (rightWires l c 0) n0
  set n1 := n0 + t0.1.length
  set t1 := buildOneNotTap l r notIdx (leftWires a 1) (rightWires l c 1) n1
  set n2 := n1 + t1.1.length
  set t2 := buildOneNotTap l r notIdx (leftWires a 2) (rightWires l c 2) n2
  rw [evalGates_append, evalGates_append, evalGates_append, evalGates_append]
  set wA := evalGates rAll.1 w
  set wN := evalGates [gNot] wA
  set w0 := evalGates t0.1 wN
  set w1 := evalGates t1.1 w0
  have hwAlen : wA.length = notIdx := by simp [wA, notIdx, evalGates_length, hwlen, n]
  have hwNlen : wN.length = n0 := by simp [wN, n0, evalGates_length, hwAlen]
  have hw0len : w0.length = n1 := by simp [w0, n1, evalGates_length, hwNlen]
  have hw1len : w1.length = n2 := by simp [w1, n2, evalGates_length, hw0len]
  have hfw_n : l + r < n := Nat.lt_trans (Nat.lt_succ_self (l + r)) (Nat.lt_succ_self (l + r + 1))
  have hn_not : n ≤ notIdx := Nat.le_add_right n rAll.1.length
  have hnot_n0 : notIdx < n0 := Nat.lt_succ_self notIdx
  have hn_n0 : n ≤ n0 := Nat.le_trans hn_not (Nat.le_of_lt hnot_n0)
  have hn0_n1 : n0 ≤ n1 := Nat.le_add_right n0 t0.1.length
  have hn1_n2 : n1 ≤ n2 := Nat.le_add_right n1 t1.1.length
  have hn_n1 : n ≤ n1 := Nat.le_trans hn_n0 hn0_n1
  have hn_n2 : n ≤ n2 := Nat.le_trans hn_n1 hn1_n2
  have hnot_n1 : notIdx < n1 := Nat.lt_of_lt_of_le hnot_n0 hn0_n1
  have hnot_n2 : notIdx < n2 := Nat.lt_of_lt_of_le hnot_n1 hn1_n2
  have hnotVal : wN.getD notIdx false = !((allRightWires l r).any (fun u => w.getD u false)) := by
    rw [← hwAlen, evalGates_singleton_last]
    simp only [gNot, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
    have hev := orChain_eval (l + r) (allRightWires l r) w (hwlen ▸ hfw_n)
      (fun u hu => hwlen ▸ allRightWires_lt l r u hu)
    rw [hwlen] at hev
    change (!wA.getD rAll.2 false) = _
    rw [hev, hfw, Bool.false_or]
  have hwN_lt : ∀ u < n, wN.getD u false = w.getD u false := by
    intro u hu
    rw [evalGates_getD_lt _ _ _ (hwAlen ▸ Nat.lt_of_lt_of_le hu hn_not),
        evalGates_getD_lt _ _ _ (hwlen ▸ hu)]
  have hw0_lt : ∀ u < n0, w0.getD u false = wN.getD u false :=
    fun u hu => evalGates_getD_lt _ _ _ (hwNlen ▸ hu)
  have hw1_lt : ∀ u < n1, w1.getD u false = w0.getD u false :=
    fun u hu => evalGates_getD_lt _ _ _ (hw0len ▸ hu)
  rcases fin3_eq k with rfl | rfl | rfl
  · rw [fin3Pick_0]
    have ht0 : t0.2 < n1 := buildOneNotTap_out_lt l r notIdx _ _ n0
    rw [evalGates_getD_lt _ _ _ (hw1len ▸ Nat.lt_of_lt_of_le ht0 hn1_n2),
        evalGates_getD_lt _ _ _ (hw0len ▸ ht0)]
    have hev := buildOneNotTap_eval l r notIdx (leftWires a 0) (rightWires l c 0) wN
      (hwNlen ▸ Nat.lt_of_lt_of_le hfw_n hn_n0)
      (by rw [hwN_lt (l + r) hfw_n, hfw])
      (hwNlen ▸ hnot_n0)
      (fun u hu => hwNlen ▸ Nat.lt_of_lt_of_le (leftWires_lt (r := r) a 0 u hu) hn_n0)
      (fun u hu => hwNlen ▸ Nat.lt_of_lt_of_le (rightWires_lt c 0 u hu) hn_n0)
    rw [hwNlen] at hev
    change w0.getD t0.2 false = _
    rw [hev, hnotVal]
    have hL0 : (leftWires a 0).any (fun u => wN.getD u false) = (leftWires a 0).any (fun u => w.getD u false) :=
      list_any_congr _ _ _ (fun u hu => hwN_lt u (leftWires_lt (r := r) a 0 u hu))
    have hR0 : (rightWires l c 0).any (fun u => wN.getD u false) = (rightWires l c 0).any (fun u => w.getD u false) :=
      list_any_congr _ _ _ (fun u hu => hwN_lt u (rightWires_lt c 0 u hu))
    rw [hL0, hR0]
  · rw [fin3Pick_1]
    have ht1 : t1.2 < n2 := buildOneNotTap_out_lt l r notIdx _ _ n1
    rw [evalGates_getD_lt _ _ _ (hw1len ▸ ht1)]
    have hev := buildOneNotTap_eval l r notIdx (leftWires a 1) (rightWires l c 1) w0
      (hw0len ▸ Nat.lt_of_lt_of_le hfw_n hn_n1)
      (by rw [hw0_lt (l + r) (Nat.lt_of_lt_of_le hfw_n hn_n0), hwN_lt (l + r) hfw_n, hfw])
      (hw0len ▸ hnot_n1)
      (fun u hu => hw0len ▸ Nat.lt_of_lt_of_le (leftWires_lt (r := r) a 1 u hu) hn_n1)
      (fun u hu => hw0len ▸ Nat.lt_of_lt_of_le (rightWires_lt c 1 u hu) hn_n1)
    rw [hw0len] at hev
    change w1.getD t1.2 false = _
    rw [hev, hw0_lt notIdx hnot_n0, hnotVal]
    have hL1 : (leftWires a 1).any (fun u => w0.getD u false) = (leftWires a 1).any (fun u => w.getD u false) :=
      list_any_congr _ _ _ (fun u hu => by
        rw [hw0_lt u (Nat.lt_of_lt_of_le (leftWires_lt (r := r) a 1 u hu) hn_n0)]
        exact hwN_lt u (leftWires_lt (r := r) a 1 u hu))
    have hR1 : (rightWires l c 1).any (fun u => w0.getD u false) = (rightWires l c 1).any (fun u => w.getD u false) :=
      list_any_congr _ _ _ (fun u hu => by
        rw [hw0_lt u (Nat.lt_of_lt_of_le (rightWires_lt c 1 u hu) hn_n0)]
        exact hwN_lt u (rightWires_lt c 1 u hu))
    rw [hL1, hR1]
  · rw [fin3Pick_2]
    have hev := buildOneNotTap_eval l r notIdx (leftWires a 2) (rightWires l c 2) w1
      (hw1len ▸ Nat.lt_of_lt_of_le hfw_n hn_n2)
      (by rw [hw1_lt (l + r) (Nat.lt_of_lt_of_le hfw_n hn_n1),
              hw0_lt (l + r) (Nat.lt_of_lt_of_le hfw_n hn_n0),
              hwN_lt (l + r) hfw_n, hfw])
      (hw1len ▸ hnot_n2)
      (fun u hu => hw1len ▸ Nat.lt_of_lt_of_le (leftWires_lt (r := r) a 2 u hu) hn_n2)
      (fun u hu => hw1len ▸ Nat.lt_of_lt_of_le (rightWires_lt c 2 u hu) hn_n2)
    rw [hw1len] at hev
    change (evalGates t2.1 w1).getD t2.2 false = _
    rw [hev, hw1_lt notIdx hnot_n1, hw0_lt notIdx hnot_n0, hnotVal]
    have hL2 : (leftWires a 2).any (fun u => w1.getD u false) = (leftWires a 2).any (fun u => w.getD u false) :=
      list_any_congr _ _ _ (fun u hu => by
        rw [hw1_lt u (Nat.lt_of_lt_of_le (leftWires_lt (r := r) a 2 u hu) hn_n1),
            hw0_lt u (Nat.lt_of_lt_of_le (leftWires_lt (r := r) a 2 u hu) hn_n0)]
        exact hwN_lt u (leftWires_lt (r := r) a 2 u hu))
    have hR2 : (rightWires l c 2).any (fun u => w1.getD u false) = (rightWires l c 2).any (fun u => w.getD u false) :=
      list_any_congr _ _ _ (fun u hu => by
        rw [hw1_lt u (Nat.lt_of_lt_of_le (rightWires_lt c 2 u hu) hn_n1),
            hw0_lt u (Nat.lt_of_lt_of_le (rightWires_lt c 2 u hu) hn_n0)]
        exact hwN_lt u (rightWires_lt c 2 u hu))
    rw [hL2, hR2]

end PEqualNP.Outside.L_lib_1288_aux

theorem PEqualNP.Outside.L_lib_1288 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (l r : Nat) (edge : Fin l → Fin r → Prop) (L : Fin l → Finset (Fin 3)) (U : Fin r → Finset (Fin 3)),
  (∀ i, (L i).Nonempty) → (∀ j, (U j).Nonempty) →
  let left := fun (i : Fin l) => List.ofFn (fun h : Fin l => decide (h=i)) ++ List.replicate r false
  let right := fun (j : Fin r) => List.ofFn (fun h : Fin l => decide (edge h j)) ++
    List.ofFn (fun h : Fin r => decide (h=j))
  let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (l+r+2) C ∧
    C.output < l+r+2+C.size ∧ ∃ p : Fin 3 → Fin (l+r+2+C.size),
      (∀ i, ∃ a ∈ L i, ∀ k, (C.wires (left i ++ [false,true])).getD (p k).val false = decide (k=a)) ∧
      (∀ j, ∃ a ∈ U j, ∀ k, (C.wires (right j ++ [false,true])).getD (p k).val false = decide (k≠a))
  let col := ∃ (a : Fin l → Fin 3) (c : Fin r → Fin 3),
    (∀ i, a i ∈ L i) ∧ (∀ j, c j ∈ U j) ∧ ∀ i j, edge i j → a i ≠ c j
  (col ↔ ∃ C, fits C ∧ PEqualNP.NotBracket.notCount C = 0) ∧
  (col → ∃ C, fits C ∧ PEqualNP.NotBracket.notCount C = 0 ∧ C.size ≤ l+2*r) ∧
  ∃ C, fits C ∧ PEqualNP.NotBracket.notCount C = 1 ∧ C.size ≤ l+3*r+7) := by
  intro l r edge L U hL hU
  dsimp only
  open PEqualNP.Outside.L_lib_1288_aux in
  have hPart2 :
      (∃ (a : Fin l → Fin 3) (c : Fin r → Fin 3),
        (∀ i, a i ∈ L i) ∧ (∀ j, c j ∈ U j) ∧ ∀ i j, edge i j → a i ≠ c j) →
      ∃ C,
        (PEqualNP.MetaComplexity.FanInTwo C ∧
         PEqualNP.MetaComplexity.NestedCover.ReadsBack (l + r + 2) C ∧
         C.output < l + r + 2 + C.size ∧
         ∃ p : Fin 3 → Fin (l + r + 2 + C.size),
           (∀ i, ∃ a ∈ L i, ∀ k,
             (C.wires (leftVec r i)).getD (p k).val false = @decide (k = a) (Classical.propDecidable _)) ∧
           (∀ j, ∃ a ∈ U j, ∀ k,
             (C.wires (rightVec edge j)).getD (p k).val false = @decide (k ≠ a) (Classical.propDecidable _))) ∧
        PEqualNP.NotBracket.notCount C = 0 ∧ C.size ≤ l + 2 * r := by
    rintro ⟨a, c, ha, hc, hcol⟩
    refine ⟨(buildMono l r a c).1, ?_, buildMono_notCount l r a c,
      le_of_eq (buildMono_size l r a c)⟩
    refine ⟨buildMono_fanInTwo l r a c, buildMono_readsBack l r a c, ?_, ?_⟩
    · exact zero_lt_add_two l r _
    · refine ⟨fun k => ⟨(buildMono l r a c).2 k, buildMono_out_lt l r a c k⟩, ?_, ?_⟩
      · intro i
        refine ⟨a i, ha i, fun k => ?_⟩
        rw [buildMono_eval l r a c _ (leftVec_len r i) (leftVec_getD_false r i) k,
          any_leftWires_leftVec r a k i, any_rightWires_leftVec c k i, Bool.or_false]
      · intro j
        refine ⟨c j, hc j, fun k => ?_⟩
        rw [buildMono_eval l r a c _ (rightVec_len edge j) (rightVec_getD_false edge j) k,
          any_rightWires_rightVec edge c k j]
        cases hLval : (leftWires a k).any (fun u => (rightVec edge j).getD u false)
        · simp
        · have hne : k ≠ c j := any_leftWires_rightVec_imp edge a c hcol k j hLval
          simp [hne]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, hPart2, ?_⟩
  · rcases hPart2 h with ⟨C, hfits, hnot, _⟩
    exact ⟨C, hfits, hnot⟩
  · rcases h with ⟨C, ⟨hfit, _, _, p, hleft, hright⟩, hnot⟩
    have hgates := fanInTwo_notCount_zero C hfit hnot
    choose a haL haEq using hleft
    choose c hcU hcEq using hright
    refine ⟨a, c, haL, hcU, fun i j hed => ?_⟩
    have h1 : (C.wires (leftVec r i)).getD (p (a i)).val false = true := by
      have := haEq i (a i)
      simpa [leftVec] using this
    have h2 : (C.wires (rightVec edge j)).getD (p (a i)).val false = true := by
      rw [wires_eq_evalGates] at h1 ⊢
      exact evalGates_mono C.gates hgates _ _
        (by rw [leftVec_len, rightVec_len]) (leftVec_le_rightVec edge i j hed) _ h1
    have h3 := hcEq j (a i)
    change (C.wires (rightVec edge j)).getD (p (a i)).val false =
      @decide (a i ≠ c j) (Classical.propDecidable _) at h3
    rw [h2] at h3
    exact (decC_iff (a i ≠ c j)).mp h3.symm
  · choose a ha using hL
    choose c hc using hU
    refine ⟨(buildOneNot l r a c).1, ?_, buildOneNot_notCount l r a c,
      le_of_eq (buildOneNot_size l r a c)⟩
    refine ⟨buildOneNot_fanInTwo l r a c, buildOneNot_readsBack l r a c, ?_, ?_⟩
    · exact zero_lt_add_two l r _
    · refine ⟨fun k => ⟨(buildOneNot l r a c).2 k, buildOneNot_out_lt l r a c k⟩, ?_, ?_⟩
      · intro i
        refine ⟨a i, ha i, fun k => ?_⟩
        change ((buildOneNot l r a c).1.wires (leftVec r i)).getD
          ((buildOneNot l r a c).2 k) false = @decide (k = a i) (Classical.propDecidable _)
        rw [buildOneNot_eval l r a c _ (leftVec_len r i) (leftVec_getD_false r i) k,
          any_leftWires_leftVec r a k i, any_allRightWires_leftVec r i,
          any_rightWires_leftVec c k i]
        simp
      · intro j
        refine ⟨c j, hc j, fun k => ?_⟩
        change ((buildOneNot l r a c).1.wires (rightVec edge j)).getD
          ((buildOneNot l r a c).2 k) false = @decide (k ≠ c j) (Classical.propDecidable _)
        rw [buildOneNot_eval l r a c _ (rightVec_len edge j) (rightVec_getD_false edge j) k,
          any_allRightWires_rightVec edge j, any_rightWires_rightVec edge c k j]
        simp
