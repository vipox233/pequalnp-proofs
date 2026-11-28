import Mathlib.Tactic
import PEqualNP.Defs

/- Circuit builders adapted from accepted L-lib-1187, and negation codes from accepted L-lib-1188. -/

namespace PEqualNP.Outside.L_lib_1220_aux.Build

open scoped Classical
open PEqualNP.CircuitLowerBounds (Circuit Gate GateOp)

/-! ### Part 1: Basic wire evaluation and Boolean order helpers -/

lemma bool_true_le_eq {b : Bool} (h : true ≤ b) : b = true := by
  cases b
  · exact absurd h (by decide)
  · rfl

lemma getElem_append_mid {α : Type*} (a c : List α) (b : α) :
    (a ++ [b] ++ c)[a.length]'(by simp) = b := by
  simp [List.append_assoc]

lemma take_succ_eq_getD (pre : List Gate) {k : ℕ} (hk : k < pre.length) :
    pre.take (k + 1) = pre.take k ++ [pre.getD k ⟨GateOp.or, []⟩] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk]
  rfl

def evalWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def wireVal (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (evalWires gs (List.ofFn x ++ [false, true])).getD w false

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma eq_not_of_isNotOp {op : GateOp} (h : isNotOp op = true) : op = GateOp.not := by
  cases op <;> simp [isNotOp] at h ⊢

def notCountL (gs : List Gate) : ℕ :=
  (gs.filter fun g => isNotOp g.op).length

lemma notCountL_eq_notCount (C : Circuit) :
    notCountL C.gates = PEqualNP.NotBracket.notCount C := by
  unfold notCountL PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> simp [isNotOp]

lemma notCountL_append (gs1 gs2 : List Gate) :
    notCountL (gs1 ++ gs2) = notCountL gs1 + notCountL gs2 := by
  simp [notCountL, List.filter_append]

lemma evalWires_length (gs : List Gate) (w : List Bool) :
    (evalWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalWires]
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons] at ih ⊢
    rw [ih, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma evalWires_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalWires (gs1 ++ gs2) w = evalWires gs2 (evalWires gs1 w) := by
  simp [evalWires, List.foldl_append]

lemma getD_append_singleton {α : Type*} (w : List α) (a d : α) (i : ℕ) :
    (w ++ [a]).getD i d = if i < w.length then w.getD i d else if i = w.length then a else d := by
  by_cases h1 : i < w.length
  · rw [if_pos h1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h1]
  · rw [if_neg h1]
    have hge : w.length ≤ i := Nat.le_of_not_lt h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
    by_cases h2 : i = w.length
    · subst h2; simp
    · rw [if_neg h2]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl

lemma evalWires_getD_prefix (gs1 gs2 : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + gs1.length) :
    (evalWires (gs1 ++ gs2) w).getD i false = (evalWires gs1 w).getD i false := by
  rw [evalWires_append]
  have hgen : ∀ (gs : List Gate) (u : List Bool), i < u.length →
      (evalWires gs u).getD i false = u.getD i false := by
    intro gs
    induction gs with
    | nil => intro u _; rfl
    | cons g gs ih =>
      intro u hu
      change (evalWires gs (u ++ [g.op.eval (g.inputs.map fun k => u.getD k false)])).getD i false = _
      rw [ih _ (by simp; omega), getD_append_singleton, if_pos hu]
  exact hgen gs2 (evalWires gs1 w) (by rw [evalWires_length]; exact hi)

lemma getD_append_le {wa wb : List Bool} (hlen : wa.length = wb.length)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) {va vb : Bool} (hv : va ≤ vb) :
    ∀ i, (wa ++ [va]).getD i false ≤ (wb ++ [vb]).getD i false := by
  intro i
  rw [getD_append_singleton, getD_append_singleton, hlen]
  by_cases h1 : i < wb.length
  · rw [if_pos h1, if_pos h1]; exact hle i
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : i = wb.length
    · rw [if_pos h2, if_pos h2]; exact hv
    · rw [if_neg h2, if_neg h2]

lemma eval_and_mono (l : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    GateOp.and.eval (l.map fun i => wa.getD i false) ≤
    GateOp.and.eval (l.map fun i => wb.getD i false) := by
  dsimp only [GateOp.eval]
  cases ha : (l.map fun i => wa.getD i false).all id
  · exact Bool.false_le _
  · have hb : (l.map fun i => wb.getD i false).all id = true := by
      rw [List.all_eq_true] at ha ⊢
      intro x hx
      rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
      have h1 : wa.getD i false = true := ha (wa.getD i false) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      exact bool_true_le_eq (h1 ▸ hle i)
    rw [hb]

lemma eval_or_mono (l : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    GateOp.or.eval (l.map fun i => wa.getD i false) ≤
    GateOp.or.eval (l.map fun i => wb.getD i false) := by
  dsimp only [GateOp.eval]
  cases ha : (l.map fun i => wa.getD i false).any id
  · exact Bool.false_le _
  · have hb : (l.map fun i => wb.getD i false).any id = true := by
      rw [List.any_eq_true] at ha ⊢
      rcases ha with ⟨x, hx, hxt⟩
      rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
      refine ⟨wb.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
      exact bool_true_le_eq (hxt ▸ hle i)
    rw [hb]

lemma eval_not_anti (l : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    GateOp.not.eval (l.map fun i => wb.getD i false) ≤
    GateOp.not.eval (l.map fun i => wa.getD i false) := by
  cases l with
  | nil => simp [GateOp.eval]
  | cons i _ =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons]
    have h := hle i
    generalize wa.getD i false = a at h ⊢
    generalize wb.getD i false = b at h ⊢
    revert h
    cases a <;> cases b <;> decide

lemma evalWires_mono_of_zero_not : ∀ (gs : List Gate),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) →
    notCountL gs = 0 →
    ∀ (wa wb : List Bool), wa.length = wb.length →
    (∀ i, wa.getD i false ≤ wb.getD i false) →
    ∀ i, (evalWires gs wa).getD i false ≤ (evalWires gs wb).getD i false
  | [], _, _, wa, wb, _, hle => hle
  | g :: gs, hfit, h0, wa, wb, hlen, hle => by
    have hne : isNotOp g.op = false := by
      cases h : isNotOp g.op
      · rfl
      · simp [notCountL, h] at h0
    have h0' : notCountL gs = 0 := by simpa [notCountL, hne] using h0
    have hfit' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
      fun g' hg' => hfit g' (List.mem_cons_of_mem g hg')
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
      have hm := hfit g (List.mem_cons_self ..)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · rw [h3] at hne; exact absurd hne (by decide)
    have hv : g.op.eval (g.inputs.map fun i => wa.getD i false) ≤
        g.op.eval (g.inputs.map fun i => wb.getD i false) := by
      rcases hg with h1 | h2
      · rw [h1]; exact eval_and_mono g.inputs wa wb hle
      · rw [h2]; exact eval_or_mono g.inputs wa wb hle
    exact evalWires_mono_of_zero_not gs hfit' h0' _ _ (by simp [hlen]) (getD_append_le hlen hle hv)

lemma inputs_le_of_pointwise {n : ℕ} {x y : Fin n → Bool}
    (hxy : ∀ u : Fin n, x u = true → y u = true) (i : ℕ) :
    (List.ofFn x ++ [false, true]).getD i false ≤
    (List.ofFn y ++ [false, true]).getD i false := by
  by_cases hi : i < n
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simp [hi]), List.getElem?_append_left (by simp [hi]),
        List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hi, dif_pos hi]
    dsimp only [Option.getD]
    cases hx : x ⟨i, hi⟩
    · exact Bool.false_le _
    · rw [hxy ⟨i, hi⟩ hx]
  · have h1 : (List.ofFn x).length ≤ i := by simp; omega
    have h2 : (List.ofFn y).length ≤ i := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right h1, List.getElem?_append_right h2]
    simp

lemma split_unique_not (gs : List Gate) (h1 : notCountL gs = 1) :
    ∃ (pre post : List Gate) (g0 : Gate),
      gs = pre ++ [g0] ++ post ∧
      g0.op = GateOp.not ∧ notCountL pre = 0 ∧ notCountL post = 0 := by
  induction gs with
  | nil => simp [notCountL] at h1
  | cons g gs ih =>
    cases hg : isNotOp g.op
    · have hgs : notCountL gs = 1 := by simpa [notCountL, hg] using h1
      rcases ih hgs with ⟨pre, post, g0, heq, hop, hpre, hpost⟩
      have hpre' : notCountL (g :: pre) = 0 := by
        have hstep : notCountL (g :: pre) = notCountL pre := by simp [notCountL, hg]
        rw [hstep, hpre]
      exact ⟨g :: pre, post, g0, by simp [heq], hop, hpre', hpost⟩
    · have hgs : notCountL gs = 0 := by
        have hstep : notCountL (g :: gs) = notCountL gs + 1 := by simp [notCountL, hg]
        omega
      exact ⟨[], gs, g, rfl, eq_not_of_isNotOp hg, rfl, hgs⟩

lemma unique_not_index_eq {pre post : List Gate} {g0 : Gate}
    (hpre0 : notCountL pre = 0) (hpost0 : notCountL post = 0)
    (j : Fin (pre ++ [g0] ++ post).length)
    (hj : ((pre ++ [g0] ++ post).get j).op = GateOp.not) :
    j.val = pre.length := by
  by_contra hne
  have hmem_not : ∀ (l : List Gate), notCountL l = 0 → ∀ g ∈ l, g.op ≠ GateOp.not := by
    intro l h0 g hg hop
    have hpos : 0 < (l.filter fun g' => isNotOp g'.op).length := by
      apply List.length_pos_of_mem
      exact List.mem_filter.mpr ⟨hg, by rw [hop]; rfl⟩
    dsimp only [notCountL] at h0
    omega
  by_cases hlt : j.val < pre.length
  · have hget : (pre ++ [g0] ++ post).get j = pre[j.val] := by
      simp only [List.get_eq_getElem, List.append_assoc]
      rw [List.getElem_append_left hlt]
    rw [hget] at hj
    exact hmem_not pre hpre0 pre[j.val] (List.getElem_mem hlt) hj
  · have hgt : pre.length + 1 ≤ j.val := by omega
    have hltp : j.val - (pre.length + 1) < post.length := by
      have := j.isLt; simp at this; omega
    have hget : (pre ++ [g0] ++ post).get j = post[j.val - (pre.length + 1)] := by
      simp only [List.get_eq_getElem]
      have hge : (pre ++ [g0]).length ≤ j.val := by simp; omega
      rw [List.getElem_append_right hge]
      congr 1; simp
    rw [hget] at hj
    exact hmem_not post hpost0 post[j.val - (pre.length + 1)] (List.getElem_mem hltp) hj

/-! ### Part 2: Constructive monotone DNF builder (for Conjunct 1 ←) -/

def WellFormed (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + 2 + j)

def Extends (n : ℕ) (gs1 gs2 : List Gate) : Prop :=
  gs1.length ≤ gs2.length ∧
  ∀ (x : Fin n → Bool) (w : ℕ), w < n + 2 + gs1.length → wireVal n gs2 x w = wireVal n gs1 x w

lemma Extends.refl (n : ℕ) (gs : List Gate) : Extends n gs gs := ⟨le_rfl, fun _ _ _ => rfl⟩

lemma Extends.trans {n : ℕ} {gs1 gs2 gs3 : List Gate}
    (h12 : Extends n gs1 gs2) (h23 : Extends n gs2 gs3) : Extends n gs1 gs3 :=
  ⟨le_trans h12.1 h23.1, fun x w hw => (h23.2 x w (by have := h12.1; omega)).trans (h12.2 x w hw)⟩

lemma wireVal_input_lt {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    wireVal n [] x u.val = x u := by
  dsimp only [wireVal, evalWires, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [u.isLt]),
      List.getElem?_ofFn, dif_pos u.isLt]
  rfl

lemma wireVal_const_false {n : ℕ} (x : Fin n → Bool) : wireVal n [] x n = false := by
  dsimp only [wireVal, evalWires, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp

lemma wireVal_const_true {n : ℕ} (x : Fin n → Bool) : wireVal n [] x (n + 1) = true := by
  dsimp only [wireVal, evalWires, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp

lemma wellFormed_push {n : ℕ} {gs : List Gate} (hwf : WellFormed n gs) (g : Gate)
    (hfit : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hrb : ∀ i ∈ g.inputs, i < n + 2 + gs.length) :
    WellFormed n (gs ++ [g]) := by
  constructor
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hwf.1 g' h1
    · rw [List.mem_singleton.mp h2]; exact hfit
  · intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        rw [getD_append_singleton, if_pos hlt]
      rw [hget] at hi; exact hwf.2 j hlt i hi
    · have heq : j = gs.length := by omega
      have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = g := by
        rw [getD_append_singleton, if_neg hlt, if_pos heq]
      rw [hget] at hi; rw [heq]; exact hrb i hi

lemma extends_push {n : ℕ} (gs : List Gate) (g : Gate) : Extends n gs (gs ++ [g]) := by
  refine ⟨by simp, fun x w hw => ?_⟩
  dsimp only [wireVal]
  rw [evalWires_append]
  set ws := evalWires gs (List.ofFn x ++ [false, true])
  have hlen : ws.length = n + 2 + gs.length := by
    dsimp only [ws]; rw [evalWires_length, List.length_append, List.length_ofFn]; simp
  change (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false = ws.getD w false
  rw [getD_append_singleton, if_pos (by omega)]

lemma wireVal_push_new {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wireVal n (gs ++ [g]) x (n + 2 + gs.length) =
    g.op.eval (g.inputs.map fun i => wireVal n gs x i) := by
  dsimp only [wireVal]
  rw [evalWires_append]
  set ws := evalWires gs (List.ofFn x ++ [false, true])
  have hlen : ws.length = n + 2 + gs.length := by
    dsimp only [ws]; rw [evalWires_length, List.length_append, List.length_ofFn]; simp
  change (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD (n + 2 + gs.length) false =
    g.op.eval (g.inputs.map fun i => ws.getD i false)
  rw [getD_append_singleton, if_neg (by omega), if_pos hlen.symm]

lemma extends_nil (n : ℕ) (gs : List Gate) : Extends n [] gs := by
  induction gs using List.reverseRecOn with
  | nil => exact Extends.refl n []
  | append_singleton l g ih => exact ih.trans (extends_push l g)

def addAndList (n : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, n + 1)
  | [w] => (gs, w)
  | w :: w' :: ws =>
    let res := addAndList n gs (w' :: ws)
    (res.1 ++ [⟨GateOp.and, [w, res.2]⟩], n + 2 + res.1.length)

lemma addAndList_spec (n : ℕ) : ∀ (ws : List ℕ) (gs : List Gate),
    WellFormed n gs → (∀ w ∈ ws, w < n + 2 + gs.length) →
    let res := addAndList n gs ws
    WellFormed n res.1 ∧ notCountL res.1 = notCountL gs ∧ Extends n gs res.1 ∧
    res.2 < n + 2 + res.1.length ∧
    (∀ x : Fin n → Bool, wireVal n res.1 x res.2 = ws.all (fun w => wireVal n gs x w))
  | [], gs, hwf, _ => by
    dsimp only [addAndList]
    refine ⟨hwf, rfl, Extends.refl n gs, by omega, fun x => ?_⟩
    rw [(extends_nil n gs).2 x (n + 1) (by simp), wireVal_const_true]; rfl
  | [w], gs, hwf, hws => by
    dsimp only [addAndList]
    refine ⟨hwf, rfl, Extends.refl n gs, hws w (List.mem_cons_self ..), fun x => by simp⟩
  | w :: w' :: ws, gs, hwf, hws => by
    have ih := addAndList_spec n (w' :: ws) gs hwf (fun u hu => hws u (List.mem_cons_of_mem w hu))
    set res := addAndList n gs (w' :: ws)
    rcases ih with ⟨hwf1, hnc1, hext1, hw1lt, hval1⟩
    have hwlt : w < n + 2 + res.1.length := by
      have := hws w (List.mem_cons_self ..); have := hext1.1; omega
    let g : Gate := ⟨GateOp.and, [w, res.2]⟩
    have hfitg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      ⟨by simp [g], by simp [g]⟩
    have hrbg : ∀ i ∈ g.inputs, i < n + 2 + res.1.length := by
      intro i hi; simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hwlt
      · exact hw1lt
    dsimp only [addAndList]
    change WellFormed n (res.1 ++ [g]) ∧ notCountL (res.1 ++ [g]) = notCountL gs ∧
      Extends n gs (res.1 ++ [g]) ∧ n + 2 + res.1.length < n + 2 + (res.1 ++ [g]).length ∧
      ∀ x : Fin n → Bool, wireVal n (res.1 ++ [g]) x (n + 2 + res.1.length) =
        (w :: w' :: ws).all (fun u => wireVal n gs x u)
    refine ⟨wellFormed_push hwf1 g hfitg hrbg, ?_, hext1.trans (extends_push res.1 g),
      by simp, fun x => ?_⟩
    · rw [notCountL_append, hnc1]; simp [notCountL, g, isNotOp]
    · rw [wireVal_push_new]
      simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
        Bool.and_true]
      rw [hext1.2 x w (hws w (List.mem_cons_self ..)), hval1 x]; rfl

def addOrList (n : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, n)
  | [w] => (gs, w)
  | w :: w' :: ws =>
    let res := addOrList n gs (w' :: ws)
    (res.1 ++ [⟨GateOp.or, [w, res.2]⟩], n + 2 + res.1.length)

lemma addOrList_spec (n : ℕ) : ∀ (ws : List ℕ) (gs : List Gate),
    WellFormed n gs → (∀ w ∈ ws, w < n + 2 + gs.length) →
    let res := addOrList n gs ws
    WellFormed n res.1 ∧ notCountL res.1 = notCountL gs ∧ Extends n gs res.1 ∧
    res.2 < n + 2 + res.1.length ∧
    (∀ x : Fin n → Bool, wireVal n res.1 x res.2 = ws.any (fun w => wireVal n gs x w))
  | [], gs, hwf, _ => by
    dsimp only [addOrList]
    refine ⟨hwf, rfl, Extends.refl n gs, by omega, fun x => ?_⟩
    rw [(extends_nil n gs).2 x n (by simp), wireVal_const_false]; rfl
  | [w], gs, hwf, hws => by
    dsimp only [addOrList]
    refine ⟨hwf, rfl, Extends.refl n gs, hws w (List.mem_cons_self ..), fun x => by simp⟩
  | w :: w' :: ws, gs, hwf, hws => by
    have ih := addOrList_spec n (w' :: ws) gs hwf (fun u hu => hws u (List.mem_cons_of_mem w hu))
    set res := addOrList n gs (w' :: ws)
    rcases ih with ⟨hwf1, hnc1, hext1, hw1lt, hval1⟩
    have hwlt : w < n + 2 + res.1.length := by
      have := hws w (List.mem_cons_self ..); have := hext1.1; omega
    let g : Gate := ⟨GateOp.or, [w, res.2]⟩
    have hfitg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      ⟨by simp [g], by simp [g]⟩
    have hrbg : ∀ i ∈ g.inputs, i < n + 2 + res.1.length := by
      intro i hi; simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hwlt
      · exact hw1lt
    dsimp only [addOrList]
    change WellFormed n (res.1 ++ [g]) ∧ notCountL (res.1 ++ [g]) = notCountL gs ∧
      Extends n gs (res.1 ++ [g]) ∧ n + 2 + res.1.length < n + 2 + (res.1 ++ [g]).length ∧
      ∀ x : Fin n → Bool, wireVal n (res.1 ++ [g]) x (n + 2 + res.1.length) =
        (w :: w' :: ws).any (fun u => wireVal n gs x u)
    refine ⟨wellFormed_push hwf1 g hfitg hrbg, ?_, hext1.trans (extends_push res.1 g),
      by simp, fun x => ?_⟩
    · rw [notCountL_append, hnc1]; simp [notCountL, g, isNotOp]
    · rw [wireVal_push_new]
      simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      rw [hext1.2 x w (hws w (List.mem_cons_self ..)), hval1 x]; rfl

def addTerms (n : ℕ) (gs : List Gate) (W : List ℕ) : List (Fin n → Bool) → List Gate × List ℕ
  | [] => (gs, [])
  | x₀ :: xs =>
    let posW := W.filter (fun w => wireVal n gs x₀ w)
    let res1 := addAndList n gs posW
    let res2 := addTerms n res1.1 W xs
    (res2.1, res1.2 :: res2.2)

lemma addTerms_spec (n : ℕ) (W : List ℕ) : ∀ (D : List (Fin n → Bool)) (gs : List Gate),
    WellFormed n gs → (∀ w ∈ W, w < n + 2 + gs.length) →
    let res := addTerms n gs W D
    WellFormed n res.1 ∧ notCountL res.1 = notCountL gs ∧ Extends n gs res.1 ∧
    (∀ u ∈ res.2, u < n + 2 + res.1.length) ∧
    (∀ y : Fin n → Bool,
      res.2.any (fun u => wireVal n res.1 y u) = true ↔
      ∃ x₀ ∈ D, ∀ w ∈ W, wireVal n gs x₀ w ≤ wireVal n gs y w)
  | [], gs, hwf, _ => by
    dsimp only [addTerms]
    refine ⟨hwf, rfl, Extends.refl n gs, fun _ h => absurd h List.not_mem_nil, fun _ => by simp⟩
  | x₀ :: xs, gs, hwf, hW => by
    set posW := W.filter (fun w => wireVal n gs x₀ w)
    have h1 := addAndList_spec n posW gs hwf (fun w hw => hW w (List.mem_of_mem_filter hw))
    set res1 := addAndList n gs posW
    rcases h1 with ⟨hwf1, hnc1, hext1, hw1lt, hval1⟩
    have h2 := addTerms_spec n W xs res1.1 hwf1
      (fun w hw => lt_of_lt_of_le (hW w hw) (by have := hext1.1; omega))
    set res2 := addTerms n res1.1 W xs
    rcases h2 with ⟨hwf2, hnc2, hext2, hws2lt, hval2⟩
    dsimp only [addTerms]
    change WellFormed n res2.1 ∧ notCountL res2.1 = notCountL gs ∧ Extends n gs res2.1 ∧
      (∀ u ∈ res1.2 :: res2.2, u < n + 2 + res2.1.length) ∧
      ∀ y : Fin n → Bool,
        (res1.2 :: res2.2).any (fun u => wireVal n res2.1 y u) = true ↔
        ∃ x₁ ∈ x₀ :: xs, ∀ w ∈ W, wireVal n gs x₁ w ≤ wireVal n gs y w
    refine ⟨hwf2, hnc2.trans hnc1, hext1.trans hext2, ?_, fun y => ?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · have := hext2.1; omega
      · exact hws2lt u hu'
    · rw [List.any_cons, Bool.or_eq_true, hext2.2 y res1.2 hw1lt, hval1 y, hval2 y]
      have hterm : posW.all (fun w => wireVal n gs y w) = true ↔
          ∀ w ∈ W, wireVal n gs x₀ w ≤ wireVal n gs y w := by
        simp only [posW, List.all_eq_true, List.mem_filter]
        constructor
        · intro hall w hw
          cases hx : wireVal n gs x₀ w
          · exact Bool.false_le _
          · rw [hall w ⟨hw, hx⟩]
        · intro hle w ⟨hw, hx⟩
          exact bool_true_le_eq (hx ▸ hle w hw)
      have htail : (∃ x₁ ∈ xs, ∀ w ∈ W, wireVal n res1.1 x₁ w ≤ wireVal n res1.1 y w) ↔
          (∃ x₁ ∈ xs, ∀ w ∈ W, wireVal n gs x₁ w ≤ wireVal n gs y w) := by
        refine exists_congr fun x₁ => and_congr_right fun _ => forall_congr' fun w =>
          imp_congr_right fun hw => ?_
        rw [hext1.2 x₁ w (hW w hw), hext1.2 y w (hW w hw)]
      rw [hterm, htail]; simp

lemma addMonotoneDNF_exists {n : ℕ} (gs : List Gate) (W : List ℕ)
    (hwf : WellFormed n gs) (hW : ∀ w ∈ W, w < n + 2 + gs.length)
    (dom : (Fin n → Bool) → Prop) (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y : Fin n → Bool, dom x → dom y →
      (∀ w ∈ W, wireVal n gs x w ≤ wireVal n gs y w) → f x ≤ f y) :
    ∃ (gs' : List Gate) (wf : ℕ),
      WellFormed n gs' ∧ notCountL gs' = notCountL gs ∧ Extends n gs gs' ∧
      wf < n + 2 + gs'.length ∧
      ∀ x : Fin n → Bool, dom x → wireVal n gs' x wf = f x := by
  let D : List (Fin n → Bool) :=
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => dom x ∧ f x = true)).toList
  have h1 := addTerms_spec n W D gs hwf hW
  set res1 := addTerms n gs W D
  rcases h1 with ⟨hwf1, hnc1, hext1, hws1lt, hval1⟩
  have h2 := addOrList_spec n res1.2 res1.1 hwf1 hws1lt
  set res2 := addOrList n res1.1 res1.2
  rcases h2 with ⟨hwf2, hnc2, hext2, hw2lt, hval2⟩
  refine ⟨res2.1, res2.2, hwf2, hnc2.trans hnc1, hext1.trans hext2, hw2lt, fun y hcy => ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [hval2 y, hval1 y]
  constructor
  · rintro ⟨x₀, hx₀D, hle⟩
    have hx₀ : dom x₀ ∧ f x₀ = true :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp hx₀D)).2
    exact bool_true_le_eq (hx₀.2 ▸ hmono x₀ y hx₀.1 hcy hle)
  · intro hfy
    refine ⟨y, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hcy, hfy⟩),
      fun _ _ => le_rfl⟩

def addEdgeOrs (n : ℕ) (gs : List Gate) : List (Fin n × Fin n) → List Gate × List ℕ
  | [] => (gs, [])
  | e :: es =>
    let g : Gate := ⟨GateOp.or, [e.1.val, e.2.val]⟩
    let w := n + 2 + gs.length
    let res := addEdgeOrs n (gs ++ [g]) es
    (res.1, w :: res.2)

lemma addEdgeOrs_spec (n : ℕ) : ∀ (es : List (Fin n × Fin n)) (gs : List Gate),
    WellFormed n gs →
    let res := addEdgeOrs n gs es
    WellFormed n res.1 ∧ notCountL res.1 = notCountL gs ∧ Extends n gs res.1 ∧
    (∀ w ∈ res.2, w < n + 2 + res.1.length) ∧
    (∀ x : Fin n → Bool,
      res.2.all (fun w => wireVal n res.1 x w) = true ↔
      ∀ e ∈ es, x e.1 = true ∨ x e.2 = true)
  | [], gs, hwf => by
    dsimp only [addEdgeOrs]
    refine ⟨hwf, rfl, Extends.refl n gs, fun _ h => absurd h List.not_mem_nil, fun _ => by simp⟩
  | e :: es, gs, hwf => by
    let g : Gate := ⟨GateOp.or, [e.1.val, e.2.val]⟩
    have hfitg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      ⟨by simp [g], by simp [g]⟩
    have hrbg : ∀ i ∈ g.inputs, i < n + 2 + gs.length := by
      intro i hi; simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> [have := e.1.isLt; have := e.2.isLt] <;> omega
    have hwf1 := wellFormed_push hwf g hfitg hrbg
    have hext1 : Extends n gs (gs ++ [g]) := extends_push gs g
    have h2 := addEdgeOrs_spec n es (gs ++ [g]) hwf1
    set res := addEdgeOrs n (gs ++ [g]) es
    rcases h2 with ⟨hwf2, hnc2, hext2, hws2lt, hval2⟩
    dsimp only [addEdgeOrs]
    change WellFormed n res.1 ∧ notCountL res.1 = notCountL gs ∧ Extends n gs res.1 ∧
      (∀ w ∈ (n + 2 + gs.length) :: res.2, w < n + 2 + res.1.length) ∧
      ∀ x : Fin n → Bool,
        ((n + 2 + gs.length) :: res.2).all (fun w => wireVal n res.1 x w) = true ↔
        ∀ e' ∈ e :: es, x e'.1 = true ∨ x e'.2 = true
    refine ⟨hwf2, ?_, hext1.trans hext2, ?_, fun x => ?_⟩
    · rw [hnc2, notCountL_append]; simp [notCountL, g, isNotOp]
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · have := hext2.1; simp at this; omega
      · exact hws2lt w hw'
    · rw [List.all_cons, Bool.and_eq_true, hval2 x]
      have hhead : wireVal n res.1 x (n + 2 + gs.length) = (x e.1 || x e.2) := by
        rw [hext2.2 x (n + 2 + gs.length) (by simp), wireVal_push_new]
        simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
          Bool.or_false]
        have he1 : wireVal n gs x e.1.val = x e.1 := by
          rw [(extends_nil n gs).2 x e.1.val (by have := e.1.isLt; simp; omega), wireVal_input_lt]
        have he2 : wireVal n gs x e.2.val = x e.2 := by
          rw [(extends_nil n gs).2 x e.2.val (by have := e.2.isLt; simp; omega), wireVal_input_lt]
        rw [he1, he2]
      rw [hhead, Bool.or_eq_true]; simp


end PEqualNP.Outside.L_lib_1220_aux.Build

namespace PEqualNP.Outside.L_lib_1220_aux.Trace

open scoped Classical
open PEqualNP.CircuitLowerBounds (Circuit Gate GateOp)

/-! ### Part 1: Wire evaluation and negation-count chain lemma -/

def evalWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma eq_not_of_isNotOp {op : GateOp} (h : isNotOp op = true) : op = GateOp.not := by
  cases op <;> simp [isNotOp] at h ⊢

def notCountL (gs : List Gate) : ℕ :=
  (gs.filter fun g => isNotOp g.op).length

def nonNotCountL (gs : List Gate) : ℕ :=
  (gs.filter fun g => !isNotOp g.op).length

lemma notCountL_eq_notCount (C : Circuit) :
    notCountL C.gates = PEqualNP.NotBracket.notCount C := by
  unfold notCountL PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> simp [isNotOp]

lemma nonNot_add_not (gs : List Gate) : nonNotCountL gs + notCountL gs = gs.length := by
  induction gs with
  | nil => simp [nonNotCountL, notCountL]
  | cons g gs ih =>
    cases h : isNotOp g.op <;> simp [nonNotCountL, notCountL, h] at ih ⊢ <;> omega

lemma notCountL_append (gs1 gs2 : List Gate) :
    notCountL (gs1 ++ gs2) = notCountL gs1 + notCountL gs2 := by
  simp [notCountL, List.filter_append]

lemma nonNotCountL_append (gs1 gs2 : List Gate) :
    nonNotCountL (gs1 ++ gs2) = nonNotCountL gs1 + nonNotCountL gs2 := by
  simp [nonNotCountL, List.filter_append]

lemma evalWires_length (gs : List Gate) (w : List Bool) :
    (evalWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalWires]
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons] at ih ⊢
    rw [ih, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma evalWires_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalWires (gs1 ++ gs2) w = evalWires gs2 (evalWires gs1 w) := by
  simp [evalWires, List.foldl_append]

lemma getD_append_singleton {α : Type*} (w : List α) (a d : α) (i : ℕ) :
    (w ++ [a]).getD i d = if i < w.length then w.getD i d else if i = w.length then a else d := by
  by_cases h1 : i < w.length
  · rw [if_pos h1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h1]
  · rw [if_neg h1]
    have hge : w.length ≤ i := Nat.le_of_not_lt h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
    by_cases h2 : i = w.length
    · subst h2; simp
    · rw [if_neg h2]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl

lemma evalWires_getD_prefix (gs1 gs2 : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + gs1.length) :
    (evalWires (gs1 ++ gs2) w).getD i false = (evalWires gs1 w).getD i false := by
  rw [evalWires_append]
  have hgen : ∀ (gs : List Gate) (u : List Bool), i < u.length →
      (evalWires gs u).getD i false = u.getD i false := by
    intro gs
    induction gs with
    | nil => intro u _; rfl
    | cons g gs ih =>
      intro u hu
      change (evalWires gs (u ++ [g.op.eval (g.inputs.map fun k => u.getD k false)])).getD i false = _
      rw [ih _ (by simp; omega), getD_append_singleton, if_pos hu]
  exact hgen gs2 (evalWires gs1 w) (by rw [evalWires_length]; exact hi)

lemma bool_true_le_eq {b : Bool} (h : true ≤ b) : b = true := by
  cases b
  · exact absurd h (by decide)
  · rfl

lemma getD_append_le {wa wb : List Bool} (hlen : wa.length = wb.length)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) {va vb : Bool} (hv : va ≤ vb) :
    ∀ i, (wa ++ [va]).getD i false ≤ (wb ++ [vb]).getD i false := by
  intro i
  rw [getD_append_singleton, getD_append_singleton, hlen]
  by_cases h1 : i < wb.length
  · rw [if_pos h1, if_pos h1]; exact hle i
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : i = wb.length
    · rw [if_pos h2, if_pos h2]; exact hv
    · rw [if_neg h2, if_neg h2]

lemma eval_and_mono (l : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    GateOp.and.eval (l.map fun i => wa.getD i false) ≤
    GateOp.and.eval (l.map fun i => wb.getD i false) := by
  dsimp only [GateOp.eval]
  cases ha : (l.map fun i => wa.getD i false).all id
  · exact Bool.false_le _
  · have hb : (l.map fun i => wb.getD i false).all id = true := by
      rw [List.all_eq_true] at ha ⊢
      intro x hx
      rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
      have h1 : wa.getD i false = true := ha (wa.getD i false) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      exact bool_true_le_eq (h1 ▸ hle i)
    rw [hb]

lemma eval_or_mono (l : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    GateOp.or.eval (l.map fun i => wa.getD i false) ≤
    GateOp.or.eval (l.map fun i => wb.getD i false) := by
  dsimp only [GateOp.eval]
  cases ha : (l.map fun i => wa.getD i false).any id
  · exact Bool.false_le _
  · have hb : (l.map fun i => wb.getD i false).any id = true := by
      rw [List.any_eq_true] at ha ⊢
      rcases ha with ⟨x, hx, hxt⟩
      rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
      refine ⟨wb.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
      exact bool_true_le_eq (hxt ▸ hle i)
    rw [hb]

lemma eval_not_anti (l : List ℕ) (wa wb : List Bool)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    GateOp.not.eval (l.map fun i => wb.getD i false) ≤
    GateOp.not.eval (l.map fun i => wa.getD i false) := by
  cases l with
  | nil => simp [GateOp.eval]
  | cons i _ =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons]
    have h := hle i
    generalize wa.getD i false = a at h ⊢
    generalize wb.getD i false = b at h ⊢
    revert h
    cases a <;> cases b <;> decide

def notCode : List Gate → List Bool → ℕ
  | [], _ => 0
  | g :: gs, w =>
    let val := g.op.eval (g.inputs.map fun i => w.getD i false)
    let rest := notCode gs (w ++ [val])
    if isNotOp g.op then
      (if val then 1 else 0) * 2 ^ (notCountL gs) + rest
    else
      rest

lemma notCode_lt : ∀ (gs : List Gate) (w : List Bool), notCode gs w < 2 ^ notCountL gs
  | [], _ => by simp [notCode, notCountL]
  | g :: gs, w => by
    have ih := notCode_lt gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    dsimp only [notCode]
    cases h : isNotOp g.op
    · simp only [Bool.false_eq_true, ↓reduceIte, notCountL, List.filter_cons, h]
      exact ih
    · have hnc : notCountL (g :: gs) = notCountL gs + 1 := by simp [notCountL, h]
      rw [hnc, pow_succ]
      simp only [↓reduceIte]
      generalize g.op.eval (g.inputs.map fun i => w.getD i false) = v at ih ⊢
      cases v <;> simp <;> omega

lemma notCode_step : ∀ (gs : List Gate),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) →
    ∀ (wa wb : List Bool), wa.length = wb.length →
    (∀ i, wa.getD i false ≤ wb.getD i false) →
    (notCode gs wb < notCode gs wa) ∨
    (notCode gs wb = notCode gs wa ∧
      ∀ i, (evalWires gs wa).getD i false ≤ (evalWires gs wb).getD i false)
  | [], _, wa, wb, _, hle => Or.inr ⟨rfl, hle⟩
  | g :: gs, hfit, wa, wb, hlen, hle => by
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      have hm := hfit g (List.mem_cons_self ..)
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
    have hfit' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
      fun g' hg' => hfit g' (List.mem_cons_of_mem g hg')
    set va := g.op.eval (g.inputs.map fun i => wa.getD i false)
    set vb := g.op.eval (g.inputs.map fun i => wb.getD i false)
    have hlen' : (wa ++ [va]).length = (wb ++ [vb]).length := by simp [hlen]
    rcases hg with hand | hor | hnot
    · have hv : va ≤ vb := by
        dsimp only [va, vb]; rw [hand]; exact eval_and_mono g.inputs wa wb hle
      have hle' := getD_append_le hlen hle hv
      have hne : isNotOp g.op = false := by rw [hand]; rfl
      have ih := notCode_step gs hfit' (wa ++ [va]) (wb ++ [vb]) hlen' hle'
      simpa [notCode, evalWires, hne, va, vb] using ih
    · have hv : va ≤ vb := by
        dsimp only [va, vb]; rw [hor]; exact eval_or_mono g.inputs wa wb hle
      have hle' := getD_append_le hlen hle hv
      have hne : isNotOp g.op = false := by rw [hor]; rfl
      have ih := notCode_step gs hfit' (wa ++ [va]) (wb ++ [vb]) hlen' hle'
      simpa [notCode, evalWires, hne, va, vb] using ih
    · have hv_anti : vb ≤ va := by
        dsimp only [va, vb]; rw [hnot]; exact eval_not_anti g.inputs wa wb hle
      have hyes : isNotOp g.op = true := by rw [hnot]; rfl
      by_cases heq : va = vb
      · have hle' := getD_append_le hlen hle (le_of_eq heq)
        have ih := notCode_step gs hfit' (wa ++ [va]) (wb ++ [vb]) hlen' hle'
        dsimp only [notCode]
        rw [hyes]
        change (if vb then 1 else 0) * 2 ^ notCountL gs + notCode gs (wb ++ [vb]) <
            (if va then 1 else 0) * 2 ^ notCountL gs + notCode gs (wa ++ [va]) ∨
            ((if vb then 1 else 0) * 2 ^ notCountL gs + notCode gs (wb ++ [vb]) =
              (if va then 1 else 0) * 2 ^ notCountL gs + notCode gs (wa ++ [va]) ∧
              ∀ i, (evalWires gs (wa ++ [va])).getD i false ≤ (evalWires gs (wb ++ [vb])).getD i false)
        rw [heq] at ih ⊢
        rcases ih with hlt | ⟨heq', hw⟩
        · exact Or.inl (Nat.add_lt_add_left hlt _)
        · exact Or.inr ⟨by rw [heq'], hw⟩
      · have hva : va = true := by
          revert hv_anti heq; cases va <;> cases vb <;> decide
        have hvb : vb = false := by
          revert hv_anti heq; cases va <;> cases vb <;> decide
        left
        dsimp only [notCode]
        rw [hyes]
        change (if vb then 1 else 0) * 2 ^ notCountL gs + notCode gs (wb ++ [vb]) <
            (if va then 1 else 0) * 2 ^ notCountL gs + notCode gs (wa ++ [va])
        rw [hva, hvb]
        have hltb := notCode_lt gs (wb ++ [false])
        simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add, one_mul]
        omega

lemma evalWires_mono_of_zero_not (gs : List Gate)
    (hfit : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (h0 : notCountL gs = 0)
    (wa wb : List Bool) (hlen : wa.length = wb.length)
    (hle : ∀ i, wa.getD i false ≤ wb.getD i false) :
    ∀ i, (evalWires gs wa).getD i false ≤ (evalWires gs wb).getD i false := by
  rcases notCode_step gs hfit wa wb hlen hle with hlt | ⟨_, hw⟩
  · exfalso
    have hlt1 := notCode_lt gs wa
    rw [h0, pow_zero] at hlt1
    omega
  · exact hw


end PEqualNP.Outside.L_lib_1220_aux.Trace

namespace PEqualNP.Outside.L_lib_1220_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket
open Build
open scoped Classical

def inputs {n : Nat} (x : Fin n → Bool) := List.ofFn x ++ [false,true]
def val {n : Nat} (C : Circuit) (x : Fin n → Bool) (w : Nat) :=
  (C.wires (inputs x)).getD w false
def code {n : Nat} (C : Circuit) (x : Fin n → Bool) :=
  Trace.notCode C.gates (inputs x)
def Active {n : Nat} (H : Finset (Fin n × Fin n)) := H.image Prod.fst ∪ H.image Prod.snd
def Covers {n : Nat} (G : Finset (Fin n × Fin n)) (x : Fin n → Bool) :=
  ∀ e ∈ G, x e.1=true ∨ x e.2=true
def Slice {n : Nat} (H : Finset (Fin n × Fin n)) (x : Fin n → Bool) :=
  ∀ i, i ∉ Active H → x i=true
def drop1 {n : Nat} (i : Fin n) : Fin n → Bool := fun j => decide (j ≠ i)
def drop2 {n : Nat} (i j : Fin n) : Fin n → Bool := fun k => decide (k ≠ i ∧ k ≠ j)

lemma code_le_one {n : Nat} (C : Circuit) (hn : notCount C ≤ 1) (x : Fin n → Bool) :
    code C x ≤ 1 := by
  have h := Trace.notCode_lt C.gates (inputs x)
  rw [Trace.notCountL_eq_notCount] at h
  have hp : 2 ^ notCount C ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hn
  dsimp [code]
  norm_num at hp
  omega

lemma fall_lt {n : Nat} (C : Circuit) (hf : FanInTwo C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i=true → y i=true)
    (w : Nat) (hx : val C x w=true) (hy : val C y w=false) :
    code C y < code C x := by
  have step := Trace.notCode_step C.gates (fun g hg => (hf g hg).1)
    (inputs x) (inputs y) (by simp [inputs]) (inputs_le_of_pointwise hxy)
  rcases step with h | ⟨_,h⟩
  · exact h
  · have bad : true ≤ false := by
      have b := h w
      change val C x w ≤ val C y w at b
      simpa only [hx,hy] using b
    exact (Bool.false_ne_true (bad rfl)).elim

lemma no_two_falls {n : Nat} (C : Circuit) (hf : FanInTwo C) (hn : notCount C ≤ 1)
    (x y z : Fin n → Bool)
    (hxy : ∀ i, x i=true → y i=true) (hyz : ∀ i, y i=true → z i=true)
    (a b : Nat) (hx : val C x a=true) (hy : val C y a=false)
    (hy' : val C y b=true) (hz : val C z b=false) : False := by
  have h1 := fall_lt C hf x y hxy a hx hy
  have h2 := fall_lt C hf y z hyz b hy' hz
  have h3 := code_le_one C hn x
  omega

lemma incident {n : Nat} (H : Finset (Fin n × Fin n)) (i : Fin n)
    (hi : i ∈ Active H) : ∃ e : ↥H, i=e.val.1 ∨ i=e.val.2 := by
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    exact ⟨⟨e,he⟩,Or.inl rfl⟩
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    exact ⟨⟨e,he⟩,Or.inr rfl⟩

lemma single_cover {n : Nat} (G : Finset (Fin n × Fin n))
    (ho : ∀ e ∈ G, e.1 < e.2) (i : Fin n) : Covers G (drop1 i) := by
  intro e he
  have ne := ne_of_lt (ho e he)
  by_cases h : e.1=i
  · right
    have : e.2 ≠ i := fun eq => ne (h.trans eq.symm)
    simp [drop1,this]
  · left; simp [drop1,h]

lemma single_xor {n : Nat} (e : Fin n × Fin n) (hne : e.1 ≠ e.2) (i : Fin n) :
    xor (drop1 i e.1) (drop1 i e.2) = decide (i=e.1 ∨ i=e.2) := by
  by_cases h1 : i=e.1 <;> by_cases h2 : i=e.2
  · exact (hne (h1.symm.trans h2)).elim
  · simp [drop1,←h1,h2,Ne.symm h2]
  · simp [drop1,←h2,h1,Ne.symm h1]
  · simp [drop1,h1,h2,Ne.symm h1,Ne.symm h2]

lemma pair_cover {n : Nat} (G : Finset (Fin n × Fin n))
    (ho : ∀ e ∈ G, e.1 < e.2) (i j : Fin n) (hij : i<j) (missing : (i,j) ∉ G) :
    Covers G (drop2 i j) := by
  intro e he
  by_cases ha : e.1 ≠ i ∧ e.1 ≠ j
  · exact Or.inl (by simp [drop2,ha])
  by_cases hb : e.2 ≠ i ∧ e.2 ≠ j
  · exact Or.inr (by simp [drop2,hb])
  have ha' : e.1=i ∨ e.1=j := by tauto
  have hb' : e.2=i ∨ e.2=j := by tauto
  have ord := ho e he
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
  · rw [ha',hb'] at ord; exact (lt_irrefl _ ord).elim
  · have eqe : e=(i,j) := Prod.ext ha' hb'
    exact (missing (eqe ▸ he)).elim
  · rw [ha',hb'] at ord; exact (not_lt_of_ge (le_of_lt hij) ord).elim
  · rw [ha',hb'] at ord; exact (lt_irrefl _ ord).elim

lemma necessary_clique {n : Nat} (G H : Finset (Fin n × Fin n))
    (ho : ∀ e ∈ G, e.1<e.2) (sub : H ⊆ G)
    (C : Circuit) (tap : ↥H → Fin (n+2+C.size)) (hf : FanInTwo C) (hn : notCount C ≤ 1)
    (good : ∀ x, Covers G x → ∀ e : ↥H,
      val C x (tap e).val = xor (x e.val.1) (x e.val.2)) :
    ∀ i ∈ Active H, ∀ j ∈ Active H, i<j → (i,j) ∈ G := by
  intro i hi j hj hij
  by_contra missing
  let x := drop2 i j
  let y := drop1 j
  let z : Fin n → Bool := fun _ => true
  have cx : Covers G x := pair_cover G ho i j hij missing
  have cy : Covers G y := single_cover G ho j
  have cz : Covers G z := fun _ _ => Or.inl rfl
  obtain ⟨ei,hii⟩ := incident H i hi
  obtain ⟨ej,hjj⟩ := incident H j hj
  have noj : ¬ (j=ei.val.1 ∨ j=ei.val.2) := by
    intro hji
    have cov := cx ei.val (sub ei.property)
    rcases hii with hi1 | hi2 <;> rcases hji with hj1 | hj2
    · exact (ne_of_lt hij) (hi1.trans hj1.symm)
    · simpa [x,drop2,←hi1,←hj2] using cov
    · simpa [x,drop2,←hi2,←hj1] using cov
    · exact (ne_of_lt hij) (hi2.trans hj2.symm)
  have hxy : ∀ k, x k=true → y k=true := by
    intro k hk
    have : k≠i ∧ k≠j := by simpa [x,drop2] using hk
    simpa [y,drop1] using this.2
  have hx : val C x (tap ei).val=true := by
    rw [good x cx ei]
    have h1 : x ei.val.1 = drop1 i ei.val.1 := by
      simp [x,drop2,drop1,Ne.symm (not_or.mp noj).1]
    have h2 : x ei.val.2 = drop1 i ei.val.2 := by
      simp [x,drop2,drop1,Ne.symm (not_or.mp noj).2]
    rw [h1,h2,single_xor _ (ne_of_lt (ho _ (sub ei.property)))]
    simp [hii]
  have hy : val C y (tap ei).val=false := by
    rw [good y cy ei]
    simpa [y,noj] using single_xor ei.val (ne_of_lt (ho _ (sub ei.property))) j
  have hy' : val C y (tap ej).val=true := by
    rw [good y cy ej]
    simpa [y,hjj] using single_xor ej.val (ne_of_lt (ho _ (sub ej.property))) j
  have hz : val C z (tap ej).val=false := by rw [good z cz ej]; rfl
  exact no_two_falls C hf hn x y z hxy (fun _ _ => rfl) _ _ hx hy hy' hz

lemma tap_zero_outside {n : Nat} (G H : Finset (Fin n × Fin n))
    (ho : ∀ e ∈ G, e.1<e.2) (sub : H ⊆ G)
    (C : Circuit) (tap : ↥H → Fin (n+2+C.size)) (hf : FanInTwo C) (hn : notCount C ≤ 1)
    (good : ∀ x, Covers G x → ∀ e : ↥H,
      val C x (tap e).val = xor (x e.val.1) (x e.val.2))
    (x : Fin n → Bool) (e : ↥H) (v : Fin n) (hv : v∈Active H)
    (h1 : v≠e.val.1) (h2 : v≠e.val.2) (hxv : x v=false) :
    val C x (tap e).val=false := by
  cases hx : val C x (tap e).val
  · rfl
  · exfalso
    let y := drop1 v
    let z : Fin n → Bool := fun _ => true
    have cy : Covers G y := single_cover G ho v
    have cz : Covers G z := fun _ _ => Or.inl rfl
    obtain ⟨f,hvf⟩ := incident H v hv
    have hxy : ∀ k, x k=true → y k=true := by
      intro k hk
      have : k≠v := by intro eq; subst k; rw [hxv] at hk; cases hk
      simpa [y,drop1] using this
    have hy : val C y (tap e).val=false := by
      rw [good y cy e]
      simpa [y,h1,h2] using single_xor e.val (ne_of_lt (ho _ (sub e.property))) v
    have hy' : val C y (tap f).val=true := by
      rw [good y cy f]
      simpa [y,hvf] using single_xor f.val (ne_of_lt (ho _ (sub f.property))) v
    have hz : val C z (tap f).val=false := by rw [good z cz f]; rfl
    exact no_two_falls C hf hn x y z hxy (fun _ _ => rfl) _ _ hx hy hy' hz


lemma necessary_tables {n : Nat} (G H : Finset (Fin n × Fin n))
    (ho : ∀ e ∈ G, e.1<e.2) (sub : H ⊆ G)
    (C : Circuit) (tap : ↥H → Fin (n+2+C.size)) (hf : FanInTwo C) (hn : notCount C ≤ 1)
    (good : ∀ x, Covers G x → ∀ e : ↥H,
      val C x (tap e).val = xor (x e.val.1) (x e.val.2))
    (F : (Fin n → Bool) → ↥H → Bool)
    (seen : ∀ x, Slice H x → ∀ e, val C x (tap e).val=F x e) :
    ∃ flag : ↥H → Bool, ∀ x, Slice H x → ∀ e : ↥H,
      F x e = (decide (∀ j ∈ Active H, j≠e.val.1 → j≠e.val.2 → x j=true) &&
        (!(x e.val.1 && x e.val.2) && (x e.val.1 || x e.val.2 || flag e))) := by
  let flag : ↥H → Bool := fun e => val C (drop2 e.val.1 e.val.2) (tap e).val
  refine ⟨flag,fun x hs e => ?_⟩
  by_cases hout : ∀ j ∈ Active H, j≠e.val.1 → j≠e.val.2 → x j=true
  · have hd : decide (∀ j ∈ Active H, j≠e.val.1 → j≠e.val.2 → x j=true)=true := decide_eq_true hout
    rw [hd]
    have beyond : ∀ j, j≠e.val.1 → j≠e.val.2 → x j=true := by
      intro j h1 h2
      by_cases hj : j∈Active H
      · exact hout j hj h1 h2
      · exact hs j hj
    have hne : e.val.1 ≠ e.val.2 := ne_of_lt (ho _ (sub e.property))
    have shape (a b : Bool) (ha : x e.val.1=a) (hb : x e.val.2=b) :
        x = fun j => if j=e.val.1 then a else if j=e.val.2 then b else true := by
      funext j
      by_cases h1 : j=e.val.1
      · simp [h1,ha]
      by_cases h2 : j=e.val.2
      · simp [h2,hb,hne.symm]
      · simp [h1,h2,beyond j h1 h2]
    cases ha : x e.val.1 <;> cases hb : x e.val.2
    · have eqx : x=drop2 e.val.1 e.val.2 := by
        rw [shape false false ha hb]
        funext j
        by_cases h1 : j=e.val.1 <;> by_cases h2 : j=e.val.2 <;> simp [drop2,h1,h2]
      have r : F x e=flag e := by rw [←seen x hs e,eqx]
      simpa [hout,ha,hb] using r
    · have eqx : x=drop1 e.val.1 := by
        rw [shape false true ha hb]
        funext j
        by_cases h1 : j=e.val.1 <;> by_cases h2 : j=e.val.2 <;> simp [drop1,h1,h2]
      have cx : Covers G x := by rw [eqx]; exact single_cover G ho _
      have r := (seen x hs e).symm.trans (good x cx e)
      simpa [hout,ha,hb] using r
    · have eqx : x=drop1 e.val.2 := by
        rw [shape true false ha hb]
        funext j
        by_cases h1 : j=e.val.1 <;> by_cases h2 : j=e.val.2 <;> simp_all [drop1]
      have cx : Covers G x := by rw [eqx]; exact single_cover G ho _
      have r := (seen x hs e).symm.trans (good x cx e)
      simpa [hout,ha,hb] using r
    · have eqx : x=(fun _ => true) := by
        rw [shape true true ha hb]
        funext j; simp
      have cx : Covers G x := by rw [eqx]; exact fun _ _ => Or.inl rfl
      have r := (seen x hs e).symm.trans (good x cx e)
      simpa [hout,ha,hb] using r
  · have bad := hout
    push_neg at bad
    obtain ⟨v,hv,h1,h2,hfalse⟩ := bad
    have hxv : x v=false := by
      cases h : x v
      · rfl
      · exact (hfalse h).elim
    have r : F x e=false := (seen x hs e).symm.trans
      (tap_zero_outside G H ho sub C tap hf hn good x e v hv h1 h2 hxv)
    simpa [hout] using r

end PEqualNP.Outside.L_lib_1220_aux

namespace PEqualNP.Outside.L_lib_1220_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket
open Build
open scoped Classical

def outside {n : Nat} (H : Finset (Fin n × Fin n)) (e : ↥H) (x : Fin n → Bool) : Bool :=
  decide (∀ j ∈ Active H, j≠e.val.1 → j≠e.val.2 → x j=true)
def allMarked {n : Nat} (H : Finset (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∀ j ∈ Active H, x j=true)
def table {n : Nat} (H : Finset (Fin n × Fin n)) (flag : ↥H → Bool)
    (e : ↥H) (x : Fin n → Bool) : Bool :=
  outside H e x && (!(x e.val.1 && x e.val.2) && (x e.val.1 || x e.val.2 || flag e))

lemma endpoints {n : Nat} (H : Finset (Fin n × Fin n)) (e : ↥H) :
    e.val.1∈Active H ∧ e.val.2∈Active H := by
  exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e.val,e.property,rfl⟩),
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.val,e.property,rfl⟩)⟩

lemma all_factor {n : Nat} (H : Finset (Fin n × Fin n)) (e : ↥H) (x : Fin n → Bool) :
    allMarked H x = (outside H e x && (x e.val.1 && x e.val.2)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [allMarked,outside,decide_eq_true_eq,Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨fun j hj _ _ => h j hj,h _ (endpoints H e).1,h _ (endpoints H e).2⟩
  · rintro ⟨hout,ha,hb⟩ j hj
    by_cases h1 : j=e.val.1
    · exact h1 ▸ ha
    by_cases h2 : j=e.val.2
    · exact h2 ▸ hb
    · exact hout j hj h1 h2

lemma table_factor {n : Nat} (H : Finset (Fin n × Fin n)) (flag : ↥H → Bool)
    (e : ↥H) (x : Fin n → Bool) :
    table H flag e x = (outside H e x &&
      (!allMarked H x && (x e.val.1 || x e.val.2 || flag e))) := by
  rw [all_factor]
  unfold table
  cases h : outside H e x <;> simp [h]

lemma table_mono {n : Nat} (H : Finset (Fin n × Fin n)) (flag : ↥H → Bool)
    (e : ↥H) (x y : Fin n → Bool) (hxy : ∀ j, x j=true → y j=true)
    (hn : (!allMarked H x) ≤ (!allMarked H y)) : table H flag e x ≤ table H flag e y := by
  change table H flag e x = true → table H flag e y = true
  intro hx
  have hh : outside H e x=true ∧ (!allMarked H x)=true ∧
      (x e.val.1 || x e.val.2 || flag e)=true := by
    have hx' := hx
    rw [table_factor] at hx'
    simpa only [Bool.and_eq_true] using hx'
  obtain ⟨hout,hnx,hend⟩ := hh
  have houty : outside H e y=true := by
    apply decide_eq_true
    have h := of_decide_eq_true hout
    exact fun j hj h1 h2 => hxy j (h j hj h1 h2)
  have hendy : (y e.val.1 || y e.val.2 || flag e)=true := by
    simp only [Bool.or_eq_true] at hend ⊢
    rcases hend with (h|h)|h
    · exact Or.inl (Or.inl (hxy _ h))
    · exact Or.inl (Or.inr (hxy _ h))
    · exact Or.inr h
  rw [table_factor]
  simpa only [Bool.and_eq_true] using
    (show outside H e y=true ∧ (!allMarked H y)=true ∧
      (y e.val.1 || y e.val.2 || flag e)=true from ⟨houty,hn hnx,hendy⟩)

lemma table_on_cover {n : Nat} (G H : Finset (Fin n × Fin n))
    (sub : H ⊆ G)
    (clique : ∀ i∈Active H, ∀ j∈Active H, i<j → (i,j)∈G)
    (flag : ↥H → Bool) (x : Fin n → Bool) (cx : Covers G x) (e : ↥H) :
    table H flag e x = xor (x e.val.1) (x e.val.2) := by
  have neighbor (v : Fin n) (hv : v∈Active H) (hxv : x v=false)
      (j : Fin n) (hj : j∈Active H) (hne : j≠v) : x j=true := by
    rcases lt_or_gt_of_ne hne with h | h
    · have cov := cx (j,v) (clique j hj v hv h)
      simpa [hxv] using cov
    · have cov := cx (v,j) (clique v hv j hj h)
      simpa [hxv] using cov
  cases ha : x e.val.1 <;> cases hb : x e.val.2
  · have cov := cx e.val (sub e.property)
    simp [ha,hb] at cov
  · have hout : outside H e x=true := by
      apply decide_eq_true
      exact fun j hj h1 _ => neighbor _ (endpoints H e).1 ha j hj h1
    simp [table,hout,ha,hb]
  · have hout : outside H e x=true := by
      apply decide_eq_true
      exact fun j hj _ h2 => neighbor _ (endpoints H e).2 hb j hj h2
    simp [table,hout,ha,hb]
  · simp [table,ha,hb]

lemma input_bank {n : Nat} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    wireVal n gs x i.val=x i := by
  rw [(extends_nil n gs).2 x i.val (by have := i.isLt; simp; omega),wireVal_input_lt]

lemma family_exists {n : Nat} {α : Type} (L : List α) (gs : List Gate) (W : List Nat)
    (wf : WellFormed n gs) (fit : ∀ w∈W, w<n+2+gs.length)
    (f : α → (Fin n → Bool) → Bool)
    (mono : ∀ a x y, (∀ w∈W, wireVal n gs x w ≤ wireVal n gs y w) → f a x ≤ f a y) :
    ∃ (gs' : List Gate) (tap : α → Nat),
      WellFormed n gs' ∧ notCountL gs'=notCountL gs ∧ Extends n gs gs' ∧
      ∀ a∈L, tap a<n+2+gs'.length ∧ ∀ x, wireVal n gs' x (tap a)=f a x := by
  classical
  induction L generalizing gs with
  | nil =>
    exact ⟨gs,fun _ => 0,wf,rfl,Extends.refl n gs,fun _ h => (List.not_mem_nil h).elim⟩
  | cons a L ih =>
    obtain ⟨gs1,tap1,wf1,nc1,ext1,good1⟩ := ih gs wf fit mono
    have fit1 : ∀ w∈W, w<n+2+gs1.length := by
      intro w hw; have := fit w hw; have := ext1.1; omega
    have mono1 : ∀ x y : Fin n → Bool, True → True →
        (∀ w∈W, wireVal n gs1 x w ≤ wireVal n gs1 y w) → f a x ≤ f a y := by
      intro x y _ _ h
      apply mono a x y
      intro w hw
      have h' := h w hw
      rwa [ext1.2 x w (fit w hw),ext1.2 y w (fit w hw)] at h'
    obtain ⟨gs2,w,wf2,nc2,ext2,fw,vw⟩ :=
      addMonotoneDNF_exists gs1 W wf1 fit1 (fun _ => True) (f a) mono1
    refine ⟨gs2,fun b => if b=a then w else tap1 b,wf2,nc2.trans nc1,ext1.trans ext2,?_⟩
    intro b hb
    by_cases heq : b=a
    · subst b; simp only [↓reduceIte]
      exact ⟨fw,fun x => vw x trivial⟩
    · simp only [heq,↓reduceIte]
      obtain ⟨fb,vb⟩ := good1 b ((List.mem_cons.mp hb).resolve_left heq)
      refine ⟨by have := ext2.1; omega,fun x => ?_⟩
      rw [ext2.2 x (tap1 b) fb,vb x]

lemma build {n : Nat} (G H : Finset (Fin n × Fin n))
    (sub : H ⊆ G)
    (clique : ∀ i∈Active H, ∀ j∈Active H, i<j → (i,j)∈G)
    (flag : ↥H → Bool) :
    ∃ (C : Circuit) (tap : ↥H → Fin (n+2+C.size)),
      FanInTwo C ∧ ReadsBack (n+2) C ∧ C.output<n+2+C.size ∧ notCount C≤1 ∧
      ∀ x, (C.eval (inputs x)=true ↔ Covers G x) ∧
        (Covers G x → ∀ e, val C x (tap e).val=xor (x e.val.1) (x e.val.2)) ∧
        (∀ e, val C x (tap e).val=table H flag e x) := by
  classical
  have wf0 : WellFormed n [] := ⟨fun _ h => (List.not_mem_nil h).elim,fun _ h => by simp at h⟩
  let U := (Active H).toList.map Fin.val
  have fitU : ∀ w∈U, w<n+2+([] : List Gate).length := by
    intro w hw; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have := i.isLt; simp; omega
  let A := addAndList n [] U
  obtain ⟨wfA,ncA,extA,fwA,vA⟩ := addAndList_spec n U [] wf0 fitU
  have aVal (x : Fin n → Bool) : wireVal n A.1 x A.2=allMarked H x := by
    rw [vA x]
    apply Bool.eq_iff_iff.mpr
    simp [U,allMarked,List.all_eq_true,wireVal_input_lt]
  let g : Gate := ⟨.not,[A.2]⟩
  let gsN := A.1++[g]
  let wn := n+2+A.1.length
  have wfN : WellFormed n gsN := wellFormed_push wfA g
    ⟨by simp [g],by simp [g]⟩ (by intro i hi; simp only [g,List.mem_singleton] at hi; subst i; exact fwA)
  have ncN : notCountL gsN=1 := by
    rw [notCountL_append,ncA]
    simp [notCountL,isNotOp,g]
  have wnFit : wn<n+2+gsN.length := by simp [wn,gsN]
  have nVal (x : Fin n → Bool) : wireVal n gsN x wn = !allMarked H x := by
    rw [wireVal_push_new]
    simp only [g,GateOp.eval,List.map_cons,List.map_nil,List.head?_cons,Option.getD_some]
    rw [aVal]
    rfl
  let Win := (List.finRange n).map Fin.val
  let W := Win++[wn]
  have fitW : ∀ w∈W, w<n+2+gsN.length := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw; have := i.isLt; omega
    · have eq : w=wn := List.mem_singleton.mp hw
      subst w
      exact wnFit
  have inW (i : Fin n) : i.val∈W := by
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
  have notW : wn∈W := List.mem_append_right _ (List.mem_singleton_self _)
  have covMono : ∀ x y : Fin n → Bool, True → True →
      (∀ w∈W, wireVal n gsN x w ≤ wireVal n gsN y w) →
      decide (Covers G x) ≤ decide (Covers G y) := by
    intro x y _ _ h hx
    have cx := of_decide_eq_true hx
    apply decide_eq_true
    intro e he
    have lexy (i : Fin n) : x i ≤ y i := by
      have h' := h i.val (inW i)
      simpa only [input_bank] using h'
    rcases cx e he with h1 | h2
    · exact Or.inl (lexy _ h1)
    · exact Or.inr (lexy _ h2)
  obtain ⟨gsC,wc,wfC,ncC,extC,fitC,valC⟩ :=
    addMonotoneDNF_exists gsN W wfN fitW (fun _ => True) (fun x => decide (Covers G x)) covMono
  have fitWC : ∀ w∈W, w<n+2+gsC.length := by
    intro w hw; have := fitW w hw; have := extC.1; omega
  have tapMono : ∀ e : ↥H, ∀ x y,
      (∀ w∈W, wireVal n gsC x w ≤ wireVal n gsC y w) →
      table H flag e x ≤ table H flag e y := by
    intro e x y h
    apply table_mono H flag e x y
    · intro i hx
      have h' := h i.val (inW i)
      rw [input_bank,input_bank] at h'
      exact h' hx
    · have h' := h wn notW
      rwa [extC.2 x wn wnFit,extC.2 y wn wnFit,nVal x,nVal y] at h'
  obtain ⟨gsF,tapF,wfF,ncF,extF,valF⟩ :=
    family_exists (Finset.univ : Finset ↥H).toList gsC W wfC fitWC
      (fun e x => table H flag e x) tapMono
  let C : Circuit := ⟨gsF,wc⟩
  have tapFit (e : ↥H) : tapF e<n+2+gsF.length :=
    (valF e (Finset.mem_toList.mpr (Finset.mem_univ e))).1
  have tapVal (e : ↥H) (x : Fin n → Bool) : wireVal n gsF x (tapF e)=table H flag e x :=
    (valF e (Finset.mem_toList.mpr (Finset.mem_univ e))).2 x
  refine ⟨C,fun e => ⟨tapF e,tapFit e⟩,wfF.1,wfF.2,?_,?_,fun x => ?_⟩
  · change wc<n+2+gsF.length
    have := extF.1; omega
  · rw [←notCountL_eq_notCount C]
    change notCountL gsF≤1
    rw [ncF,ncC,ncN]
  · constructor
    · change wireVal n gsF x wc=true ↔ Covers G x
      rw [extF.2 x wc fitC,valC x trivial]
      simp
    · constructor
      · intro cx e
        change wireVal n gsF x (tapF e)=_
        rw [tapVal e x]
        exact table_on_cover G H sub clique flag x cx e
      · intro e
        exact tapVal e x

end PEqualNP.Outside.L_lib_1220_aux


namespace PEqualNP.Outside.L_lib_1220_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

lemma classification {n : Nat} (G H : Finset (Fin n × Fin n))
    (F : (Fin n → Bool) → ↥H → Bool)
    (ho : ∀ e∈G, e.1<e.2) (sub : H ⊆ G) :
    ((∃ (C : Circuit) (tap : ↥H → Fin (n+2+C.size)),
      FanInTwo C ∧ ReadsBack (n+2) C ∧ C.output<n+2+C.size ∧ notCount C≤1 ∧
      ∀ x, (C.eval (inputs x)=true ↔ Covers G x) ∧
        (Covers G x → ∀ e, val C x (tap e).val=xor (x e.val.1) (x e.val.2)) ∧
        (Slice H x → ∀ e, val C x (tap e).val=F x e)) ↔
      (∀ i∈Active H, ∀ j∈Active H, i<j → (i,j)∈G) ∧
      ∃ flag : ↥H → Bool, ∀ x, Slice H x → ∀ e, F x e=table H flag e x) := by
  constructor
  · rintro ⟨C,tap,hf,hr,hw,hn,spec⟩
    have good := fun x cx e => (spec x).2.1 cx e
    have seen := fun x hs e => (spec x).2.2 hs e
    exact ⟨necessary_clique G H ho sub C tap hf hn good,
      necessary_tables G H ho sub C tap hf hn good F seen⟩
  · rintro ⟨clique,flag,hflag⟩
    obtain ⟨C,tap,hf,hr,hw,hn,spec⟩ := build G H sub clique flag
    refine ⟨C,tap,hf,hr,hw,hn,fun x => ⟨(spec x).1,(spec x).2.1,fun hs e => ?_⟩⟩
    exact ((spec x).2.2 e).trans (hflag x hs e).symm

end PEqualNP.Outside.L_lib_1220_aux


theorem PEqualNP.Outside.L_lib_1220 :
∀ (n : Nat) (G H : Finset (Fin n × Fin n)) (F : (Fin n → Bool) → ↥H → Bool),
  (∀ e ∈ G, e.1 < e.2) → H ⊆ G →
  let U := H.image Prod.fst ∪ H.image Prod.snd
  let cover := fun x : Fin n → Bool => ∀ e ∈ G, x e.1=true ∨ x e.2=true
  let sat := fun x : Fin n → Bool => ∀ i, i ∉ U → x i=true
  ((∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : ↥H → Fin (n+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ ∀ x : Fin n → Bool,
      let w := List.ofFn x ++ [false,true]
      (C.eval w = true ↔ cover x) ∧
      (cover x → ∀ e, (C.wires w).getD (tap e).val false = xor (x e.val.1) (x e.val.2)) ∧
      (sat x → ∀ e, (C.wires w).getD (tap e).val false = F x e)) ↔
    (∀ i ∈ U, ∀ j ∈ U, i < j → (i,j) ∈ G) ∧
    ∃ flag : ↥H → Bool, ∀ x, sat x → ∀ e : ↥H,
      F x e = (decide (∀ j ∈ U, j ≠ e.val.1 → j ≠ e.val.2 → x j=true) &&
        (!(x e.val.1 && x e.val.2) && (x e.val.1 || x e.val.2 || flag e)))) := by
  intro n G H F ho sub
  exact PEqualNP.Outside.L_lib_1220_aux.classification G H F ho sub
