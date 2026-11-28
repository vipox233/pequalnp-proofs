import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1187_aux

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

/-! ### Part 3: Conjunct 1 — Characterization of the guard feeding the sole NOT gate -/

lemma cover_allExcept_singleton {n : ℕ} (G : Finset (Fin n × Fin n))
    (hltG : ∀ e ∈ G, e.1 < e.2) (v : Fin n) :
    ∀ e ∈ G, (fun u => decide (u ≠ v)) e.1 = true ∨ (fun u => decide (u ≠ v)) e.2 = true := by
  intro e he
  have hne : e.1 ≠ e.2 := ne_of_lt (hltG e he)
  by_cases h1 : e.1 = v
  · right; simp [h1 ▸ hne.symm]
  · left; simp [h1]

lemma one_not_guard_step {n : ℕ} (C : Circuit)
    (hfit : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (hnc1 : PEqualNP.NotBracket.notCount C = 1)
    (pre post : List Gate) (g0 : Gate)
    (hgs_eq : C.gates = pre ++ [g0] ++ post)
    (hg0_op : g0.op = GateOp.not) (hpre0 : notCountL pre = 0) (hpost0 : notCountL post = 0)
    (w : ℕ) (hhead : g0.inputs.head? = some w) :
    (∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      (C.wires (List.ofFn x ++ [false, true])).getD w false = true →
      (C.wires (List.ofFn y ++ [false, true])).getD w false = true) ∧
    (∀ x : Fin n → Bool,
      (C.wires (List.ofFn x ++ [false, true])).getD (n + 2 + pre.length) false =
      !((C.wires (List.ofFn x ++ [false, true])).getD w false)) ∧
    (∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      (C.wires (List.ofFn x ++ [false, true])).getD w false =
      (C.wires (List.ofFn y ++ [false, true])).getD w false →
      ∀ k, (C.wires (List.ofFn x ++ [false, true])).getD k false ≤
        (C.wires (List.ofFn y ++ [false, true])).getD k false) := by
  have hw_lt : w < n + 2 + pre.length := by
    have hj_lt : pre.length < C.gates.length := by rw [hgs_eq]; simp
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C pre.length = g0 := by
      dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
      rw [hgs_eq, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp),
          List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
    have hw_in : w ∈ g0.inputs := List.mem_of_head? hhead
    exact hrb pre.length hj_lt w (hgate ▸ hw_in)
  have hfit_pre : ∀ g ∈ pre, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
    fun g hg => (hfit g (by rw [hgs_eq]; simp [hg])).1
  have hfit_post : ∀ g ∈ post, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
    fun g hg => (hfit g (by rw [hgs_eq]; simp [hg])).1
  have hg_pre : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x ++ [false, true])).getD w false =
      (evalWires pre (List.ofFn x ++ [false, true])).getD w false := by
    intro x
    change (evalWires C.gates _).getD w false = _
    rw [hgs_eq, List.append_assoc, evalWires_getD_prefix pre ([g0] ++ post) _ w (by simp; omega)]
  have hg0_eval : ∀ x : Fin n → Bool,
      g0.op.eval (g0.inputs.map fun i => (evalWires pre (List.ofFn x ++ [false, true])).getD i false) =
      !((C.wires (List.ofFn x ++ [false, true])).getD w false) := by
    intro x
    rw [hg0_op, hg_pre x]
    cases hin : g0.inputs with
    | nil => rw [hin] at hhead; cases hhead
    | cons a as =>
      rw [hin] at hhead; cases hhead
      simp [GateOp.eval]
  have hval_not : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x ++ [false, true])).getD (n + 2 + pre.length) false =
      !((C.wires (List.ofFn x ++ [false, true])).getD w false) := by
    intro x
    change (evalWires C.gates _).getD (n + 2 + pre.length) false = _
    rw [hgs_eq, evalWires_getD_prefix (pre ++ [g0]) post _ (n + 2 + pre.length) (by simp),
        evalWires_append]
    set ws := evalWires pre (List.ofFn x ++ [false, true])
    have hws_len : ws.length = n + 2 + pre.length := by
      dsimp only [ws]; rw [evalWires_length]; simp
    change (ws ++ [g0.op.eval (g0.inputs.map fun i => ws.getD i false)]).getD (n + 2 + pre.length) false = _
    rw [getD_append_singleton, if_neg (by omega), if_pos hws_len.symm]
    exact hg0_eval x
  refine ⟨?_, hval_not, ?_⟩
  · intro x y hxy hgx
    rw [hg_pre x] at hgx
    rw [hg_pre y]
    have hm := evalWires_mono_of_zero_not pre hfit_pre hpre0
      (List.ofFn x ++ [false, true]) (List.ofFn y ++ [false, true]) (by simp)
      (inputs_le_of_pointwise hxy) w
    rw [hgx] at hm
    exact bool_true_le_eq hm
  · intro x y hxy hgeq k
    change (evalWires C.gates _).getD k false ≤ (evalWires C.gates _).getD k false
    rw [hgs_eq, evalWires_append, evalWires_append, evalWires_append, evalWires_append]
    apply evalWires_mono_of_zero_not post hfit_post hpost0
    · simp [evalWires_length]
    · have hpre_m := evalWires_mono_of_zero_not pre hfit_pre hpre0
        (List.ofFn x ++ [false, true]) (List.ofFn y ++ [false, true]) (by simp)
        (inputs_le_of_pointwise hxy)
      have hlen_p : (evalWires pre (List.ofFn x ++ [false, true])).length =
          (evalWires pre (List.ofFn y ++ [false, true])).length := by simp [evalWires_length]
      have hveq : g0.op.eval (g0.inputs.map fun i => (evalWires pre (List.ofFn x ++ [false, true])).getD i false) =
          g0.op.eval (g0.inputs.map fun i => (evalWires pre (List.ofFn y ++ [false, true])).getD i false) := by
        rw [hg0_eval x, hg0_eval y, hgeq]
      exact getD_append_le hlen_p hpre_m (le_of_eq hveq)

lemma conjunct1_fwd {n : ℕ} (G H : Finset (Fin n × Fin n))
    (hltG : ∀ e ∈ G, e.1 < e.2) (hHG : H ⊆ G)
    (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size))
    (hfit : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (hnc1 : PEqualNP.NotBracket.notCount C = 1)
    (hspec : ∀ x : Fin n → Bool,
      let wires := List.ofFn x ++ [false, true]
      (C.eval wires = true ↔ ∀ e ∈ G, x e.1 = true ∨ x e.2 = true) ∧
      ((∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        ∀ e, (C.wires wires).getD (tap e).val false = xor (x e.val.1) (x e.val.2)))
    (g : (Fin n → Bool) → Bool)
    (hg_mono : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (j : Fin C.gates.length) (w : ℕ)
    (hj_op : (C.gates.get j).op = GateOp.not)
    (hj_head : (C.gates.get j).inputs.head? = some w)
    (hg_eq : ∀ x : Fin n → Bool, (C.wires (List.ofFn x ++ [false, true])).getD w false = g x) :
    let active := H.image Prod.fst ∪ H.image Prod.snd
    let adj := fun u v : Fin n => (u, v) ∈ G ∨ (v, u) ∈ G
    let cover := fun x : Fin n → Bool => ∀ e ∈ G, x e.1 = true ∨ x e.2 = true
    (∀ i ∈ active, ∀ k ∈ active, i ≠ k → adj i k) ∧
    (∀ x, g x = true → ∀ i ∈ active, x i = true) ∧
    (∀ x, cover x → (∀ i ∈ active, x i = true) →
      (∃ i ∈ active, ∀ k, adj i k → x k = true) → g x = true) := by
  let active := H.image Prod.fst ∪ H.image Prod.snd
  let adj := fun u v : Fin n => (u, v) ∈ G ∨ (v, u) ∈ G
  let cover := fun x : Fin n → Bool => ∀ e ∈ G, x e.1 = true ∨ x e.2 = true
  have hncL : notCountL C.gates = 1 := (notCountL_eq_notCount C).trans hnc1
  rcases split_unique_not C.gates hncL with ⟨pre, post, g0, hgs_eq, hg0_op, hpre0, hpost0⟩
  have hj_val : j.val = pre.length := by
    have hj' : ((pre ++ [g0] ++ post).get ⟨j.val, hgs_eq ▸ j.isLt⟩).op = GateOp.not := by
      simpa [List.get_eq_getElem, hgs_eq] using hj_op
    exact unique_not_index_eq hpre0 hpost0 ⟨j.val, hgs_eq ▸ j.isLt⟩ hj'
  have hg0_eq : C.gates.get j = g0 := by
    simp only [List.get_eq_getElem]
    have h1 : C.gates[j.val] = (pre ++ [g0] ++ post)[pre.length]'(by simp) := by
      simp only [hgs_eq, hj_val]
    rw [h1, getElem_append_mid]
  rw [hg0_eq] at hj_head
  rcases one_not_guard_step C hfit hrb hnc1 pre post g0 hgs_eq hg0_op hpre0 hpost0 w hj_head with
    ⟨_, _, hmono_wires⟩
  -- Key drop lemma: if x <= y are covers and some e in H drops true -> false, then g x = false ∧ g y = true
  have hdrop : ∀ x y : Fin n → Bool, cover x → cover y →
      (∀ u, x u = true → y u = true) →
      (∃ e ∈ H, xor (x e.1) (x e.2) = true ∧ xor (y e.1) (y e.2) = false) →
      g x = false ∧ g y = true := by
    intro x y hcx hcy hxy ⟨e, heH, hxe, hye⟩
    have hne : g x ≠ g y := by
      intro heq
      have hw_le := hmono_wires x y hxy (by rw [hg_eq x, hg_eq y]; exact heq) (tap ⟨e, heH⟩).val
      rw [(hspec x).2 hcx ⟨e, heH⟩, (hspec y).2 hcy ⟨e, heH⟩, hxe, hye] at hw_le
      exact absurd hw_le (by decide)
    cases hgx : g x
    · cases hgy : g y
      · exact absurd (hgx.trans hgy.symm) hne
      · exact ⟨rfl, rfl⟩
    · have hgy := hg_mono x y hxy hgx
      exact absurd (hgx.trans hgy.symm) hne
  have hinc_edge : ∀ i ∈ active, ∃ e ∈ H, e.1 = i ∨ e.2 = i := by
    intro i hi
    rcases Finset.mem_union.mp hi with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨e, heH, rfl⟩; exact ⟨e, heH, Or.inl rfl⟩
    · rcases Finset.mem_image.mp h2 with ⟨e, heH, rfl⟩; exact ⟨e, heH, Or.inr rfl⟩
  have hdrop_single : ∀ i ∈ active, g (fun u => decide (u ≠ i)) = false := by
    intro i hi
    rcases hinc_edge i hi with ⟨e, heH, hie⟩
    have hne_e : e.1 ≠ e.2 := ne_of_lt (hltG e (hHG heH))
    have hcov1 := cover_allExcept_singleton G hltG i
    have hcov2 : cover (fun _ => true) := fun _ _ => Or.inl rfl
    have hxor1 : xor (decide (e.1 ≠ i)) (decide (e.2 ≠ i)) = true := by
      rcases hie with rfl | rfl
      · simp [hne_e.symm]
      · simp [hne_e]
    exact (hdrop _ _ hcov1 hcov2 (fun _ _ => rfl) ⟨e, heH, hxor1, by rfl⟩).1
  refine ⟨?_, ?_, ?_⟩
  · -- active is a clique
    intro i hi k hk hik
    by_contra hnotadj
    let x2 : Fin n → Bool := fun u => decide (u ≠ i ∧ u ≠ k)
    let x1 : Fin n → Bool := fun u => decide (u ≠ k)
    let x0 : Fin n → Bool := fun _ => true
    have hcov2 : cover x2 := by
      intro e he
      have hne : e.1 ≠ e.2 := ne_of_lt (hltG e he)
      by_cases h1 : e.1 = i ∨ e.1 = k
      · by_cases h2 : e.2 = i ∨ e.2 = k
        · exfalso
          rcases h1 with rfl | rfl <;> rcases h2 with h2' | h2'
          · exact hne h2'.symm
          · exact hnotadj (Or.inl (by rwa [← h2']))
          · exact hnotadj (Or.inr (by rwa [← h2']))
          · exact hne h2'.symm
        · right; simp only [x2, decide_eq_true_eq]; tauto
      · left; simp only [x2, decide_eq_true_eq]; tauto
    have hcov1 := cover_allExcept_singleton G hltG k
    have hcov0 : cover x0 := fun _ _ => Or.inl rfl
    rcases hinc_edge i hi with ⟨e, heH, hie⟩
    have heG : e ∈ G := hHG heH
    have hne_e : e.1 ≠ e.2 := ne_of_lt (hltG e heG)
    have hxor_21 : xor (x2 e.1) (x2 e.2) = true ∧ xor (x1 e.1) (x1 e.2) = false := by
      rcases hie with rfl | rfl
      · have he2k : e.2 ≠ k := fun h => hnotadj (Or.inl (h ▸ heG))
        simp [x2, x1, hne_e.symm, hik, he2k]
      · have he1k : e.1 ≠ k := fun h => hnotadj (Or.inr (h ▸ heG))
        simp [x2, x1, hne_e, hik, he1k]
    have hg1_true : g x1 = true :=
      (hdrop x2 x1 hcov2 hcov1 (fun u hu => by simp only [x2, x1, decide_eq_true_eq] at hu ⊢; exact hu.2)
        ⟨e, heH, hxor_21⟩).2
    have hg1_false : g x1 = false := hdrop_single k hk
    rw [hg1_true] at hg1_false
    exact Bool.false_ne_true hg1_false.symm
  · -- g x = true → ∀ i ∈ active, x i = true
    intro x hgx i hi
    by_contra hxi
    have hxf : x i = false := Bool.eq_false_iff.mpr hxi
    have hle : ∀ u, x u = true → decide (u ≠ i) = true := by
      intro u hu
      simp only [decide_eq_true_eq]
      rintro rfl
      rw [hxf] at hu; exact Bool.false_ne_true hu
    have h1 := hg_mono x (fun u => decide (u ≠ i)) hle hgx
    rw [hdrop_single i hi] at h1
    exact Bool.false_ne_true h1
  · -- cover x → active all true → removable i ∈ active → g x = true
    intro x hcx hall ⟨i, hi, hnb⟩
    let x' : Fin n → Bool := Function.update x i false
    have hcx' : cover x' := by
      intro e he
      have hne : e.1 ≠ e.2 := ne_of_lt (hltG e he)
      by_cases h1 : e.1 = i
      · right
        have h2ne : e.2 ≠ i := h1 ▸ hne.symm
        simp only [x', Function.update_of_ne h2ne]
        exact hnb e.2 (Or.inl (h1 ▸ he))
      · by_cases h2 : e.2 = i
        · left
          simp only [x', Function.update_of_ne h1]
          exact hnb e.1 (Or.inr (h2 ▸ he))
        · simp only [x', Function.update_of_ne h1, Function.update_of_ne h2]
          exact hcx e he
    have hle : ∀ u, x' u = true → x u = true := by
      intro u hu
      by_cases hui : u = i
      · subst hui; simp [x'] at hu
      · simpa [x', Function.update_of_ne hui] using hu
    rcases hinc_edge i hi with ⟨e, heH, hie⟩
    have hne_e : e.1 ≠ e.2 := ne_of_lt (hltG e (hHG heH))
    have he1_act : e.1 ∈ active := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, heH, rfl⟩)
    have he2_act : e.2 ∈ active := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, heH, rfl⟩)
    have hxe1 : x e.1 = true := hall e.1 he1_act
    have hxe2 : x e.2 = true := hall e.2 he2_act
    have hxor_x' : xor (x' e.1) (x' e.2) = true := by
      rcases hie with rfl | rfl
      · simp [x', Function.update_of_ne hne_e.symm, hxe2]
      · simp [x', Function.update_of_ne hne_e, hxe1]
    have hxor_x : xor (x e.1) (x e.2) = false := by rw [hxe1, hxe2]; rfl
    exact (hdrop x' x hcx' hcx hle ⟨e, heH, hxor_x', hxor_x⟩).2

lemma conjunct1_bwd {n : ℕ} (G H : Finset (Fin n × Fin n))
    (hHG : H ⊆ G)
    (g : (Fin n → Bool) → Bool)
    (hg_mono : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (hclique : ∀ i ∈ H.image Prod.fst ∪ H.image Prod.snd,
      ∀ k ∈ H.image Prod.fst ∪ H.image Prod.snd, i ≠ k → (i, k) ∈ G ∨ (k, i) ∈ G)
    (hupper : ∀ x, g x = true → ∀ i ∈ H.image Prod.fst ∪ H.image Prod.snd, x i = true)
    (hlower : ∀ x, (∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
      (∀ i ∈ H.image Prod.fst ∪ H.image Prod.snd, x i = true) →
      (∃ i ∈ H.image Prod.fst ∪ H.image Prod.snd, ∀ k, ((i, k) ∈ G ∨ (k, i) ∈ G) → x k = true) →
      g x = true) :
    ∃ C : Circuit,
      (PEqualNP.MetaComplexity.FanInTwo C ∧
       PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
       C.output < n + 2 + C.size) ∧
      (∃ tap : ↥H → Fin (n + 2 + C.size), ∀ x : Fin n → Bool,
        let wires := List.ofFn x ++ [false, true]
        (C.eval wires = true ↔ ∀ e ∈ G, x e.1 = true ∨ x e.2 = true) ∧
        ((∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
          ∀ e, (C.wires wires).getD (tap e).val false = xor (x e.val.1) (x e.val.2))) ∧
      PEqualNP.NotBracket.notCount C = 1 ∧
      ∃ (j : Fin C.gates.length) (w : ℕ),
        (C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some w ∧
        ∀ x : Fin n → Bool, (C.wires (List.ofFn x ++ [false, true])).getD w false = g x := by
  let active := H.image Prod.fst ∪ H.image Prod.snd
  let cover : (Fin n → Bool) → Prop := fun x => ∀ e ∈ G, x e.1 = true ∨ x e.2 = true
  have hwf0 : WellFormed n [] := ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => by simp at h⟩
  let Win : List ℕ := (List.finRange n).map Fin.val
  have hWin_lt : ∀ w ∈ Win, w < n + 2 + ([] : List Gate).length := by
    intro w hw; rcases List.mem_map.mp hw with ⟨u, _, rfl⟩; have := u.isLt; simp; omega
  -- 1. Build monotone DNF for g on all inputs
  have hg_mono' : ∀ x y : Fin n → Bool, True → True →
      (∀ w ∈ Win, wireVal n [] x w ≤ wireVal n [] y w) → g x ≤ g y := by
    intro x y _ _ hWle
    cases hgx : g x
    · exact Bool.false_le _
    · have hxy : ∀ u : Fin n, x u = true → y u = true := by
        intro u hxu
        have h := hWle u.val (List.mem_map.mpr ⟨u, List.mem_finRange u, rfl⟩)
        rw [wireVal_input_lt, wireVal_input_lt, hxu] at h
        exact bool_true_le_eq h
      rw [hg_mono x y hxy hgx]
  rcases addMonotoneDNF_exists [] Win hwf0 hWin_lt (fun _ => True) g hg_mono' with
    ⟨gs1, wg, hwf1, hnc1, hext1, hwg_lt, hwg_val⟩
  -- 2. Append the sole NOT gate reading wg
  let gnot : Gate := ⟨GateOp.not, [wg]⟩
  let gs2 := gs1 ++ [gnot]
  let wNot := n + 2 + gs1.length
  let j0 := gs1.length
  have hfitnot : gnot.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      gnot.inputs.length ≤ 2 := ⟨by simp [gnot], by simp [gnot]⟩
  have hrbnot : ∀ i ∈ gnot.inputs, i < n + 2 + gs1.length := by
    intro i hi; simp only [gnot, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi; exact hwg_lt
  have hwf2 := wellFormed_push hwf1 gnot hfitnot hrbnot
  have hext12 : Extends n gs1 gs2 := extends_push gs1 gnot
  have hnc2 : notCountL gs2 = 1 := by
    dsimp only [gs2]; rw [notCountL_append, hnc1]; simp [notCountL, gnot, isNotOp]
  have hwNot_lt : wNot < n + 2 + gs2.length := by dsimp only [gs2, wNot]; simp
  have hwNot_val : ∀ x : Fin n → Bool, wireVal n gs2 x wNot = !(g x) := by
    intro x
    dsimp only [gs2, wNot]
    rw [wireVal_push_new]
    simp only [gnot, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
    rw [hwg_val x trivial]
  -- 3. Build cover wire
  have hedge := addEdgeOrs_spec n G.toList gs2 hwf2
  set resE := addEdgeOrs n gs2 G.toList
  rcases hedge with ⟨hwfE, hncE, hext2E, hwsElt, hvalE⟩
  have hcov := addAndList_spec n resE.2 resE.1 hwfE hwsElt
  set resC := addAndList n resE.1 resE.2
  rcases hcov with ⟨hwfC, hncC, hextEC, wCov_lt, hvalC⟩
  let gs3 := resC.1
  let wCov := resC.2
  have hext23 : Extends n gs2 gs3 := hext2E.trans hextEC
  have hnc3 : notCountL gs3 = 1 := by dsimp only [gs3]; rw [hncC, hncE, hnc2]
  have hcov_spec : ∀ x : Fin n → Bool, wireVal n gs3 x wCov = true ↔ cover x := by
    intro x; dsimp only [gs3, wCov]; rw [hvalC x, hvalE x]; simp only [cover, Finset.mem_toList]
  -- 4. Build monotone DNF taps for each e in H over W := wNot :: Win
  let W : List ℕ := wNot :: Win
  have hW3_lt : ∀ w ∈ W, w < n + 2 + gs3.length := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hwin
    · have := hext23.1; omega
    · rcases List.mem_map.mp hwin with ⟨u, _, rfl⟩; have := u.isLt; omega
  have hparity_mono : ∀ e : ↥H, ∀ x y : Fin n → Bool, cover x → cover y →
      (∀ w ∈ W, wireVal n gs3 x w ≤ wireVal n gs3 y w) →
      xor (x e.val.1) (x e.val.2) ≤ xor (y e.val.1) (y e.val.2) := by
    intro e x y hcx hcy hWle
    cases hxe : xor (x e.val.1) (x e.val.2)
    · exact Bool.false_le _
    · cases hye : xor (y e.val.1) (y e.val.2)
      · exfalso
        have hxy : ∀ u : Fin n, x u = true → y u = true := by
          intro u hxu
          have h := hWle u.val (List.mem_cons_of_mem wNot (List.mem_map.mpr ⟨u, List.mem_finRange u, rfl⟩))
          rw [(extends_nil n gs3).2 x u.val (by have := u.isLt; simp; omega), wireVal_input_lt,
              (extends_nil n gs3).2 y u.val (by have := u.isLt; simp; omega), wireVal_input_lt, hxu] at h
          exact bool_true_le_eq h
        have hnot_le : (!(g x)) ≤ (!(g y)) := by
          have h := hWle wNot (List.mem_cons_self ..)
          rwa [hext23.2 x wNot hwNot_lt, hext23.2 y wNot hwNot_lt, hwNot_val x, hwNot_val y] at h
        have hxe_cov : x e.val.1 = true ∨ x e.val.2 = true := hcx e.val (hHG e.property)
        have hex_i : ∃ i ∈ active, x i = false ∧ y i = true := by
          have h1act : e.val.1 ∈ active := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩)
          have h2act : e.val.2 ∈ active := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.val, e.property, rfl⟩)
          cases hx1 : x e.val.1 <;> cases hx2 : x e.val.2
          · rcases hxe_cov with h | h <;> simp_all
          · have hy2 : y e.val.2 = true := hxy e.val.2 hx2
            have hy1 : y e.val.1 = true := by
              cases h : y e.val.1
              · rw [h, hy2] at hye; exact absurd hye (by decide)
              · rfl
            exact ⟨e.val.1, h1act, hx1, hy1⟩
          · have hy1 : y e.val.1 = true := hxy e.val.1 hx1
            have hy2 : y e.val.2 = true := by
              cases h : y e.val.2
              · rw [hy1, h] at hye; exact absurd hye (by decide)
              · rfl
            exact ⟨e.val.2, h2act, hx2, hy2⟩
          · rw [hx1, hx2] at hxe; exact absurd hxe (by decide)
        rcases hex_i with ⟨i, hi_act, hxi_f, hyi_t⟩
        have hgx_f : g x = false := by
          cases h : g x
          · rfl
          · have ht := hupper x h i hi_act; rw [hxi_f] at ht; exact absurd ht (by decide)
        have hgy_f : g y = false := by
          rw [hgx_f] at hnot_le
          have h1 := bool_true_le_eq hnot_le
          cases h : g y
          · rfl
          · rw [h] at h1; exact absurd h1 (by decide)
        have hy_all_act : ∀ u ∈ active, y u = true := by
          intro u hu
          by_cases hui : u = i
          · exact hui ▸ hyi_t
          · have hadj := hclique i hi_act u hu (Ne.symm hui)
            have hxu : x u = true := by
              rcases hadj with h1 | h2
              · rcases hcx (i, u) h1 with h | h
                · rw [hxi_f] at h; exact absurd h (by decide)
                · exact h
              · rcases hcx (u, i) h2 with h | h
                · exact h
                · rw [hxi_f] at h; exact absurd h (by decide)
            exact hxy u hxu
        have hy_nb : ∀ k, ((i, k) ∈ G ∨ (k, i) ∈ G) → y k = true := by
          intro k hk
          have hxk : x k = true := by
            rcases hk with h1 | h2
            · rcases hcx (i, k) h1 with h | h
              · rw [hxi_f] at h; exact absurd h (by decide)
              · exact h
            · rcases hcx (k, i) h2 with h | h
              · exact h
              · rw [hxi_f] at h; exact absurd h (by decide)
          exact hxy k hxk
        have hgy_t := hlower y hcy hy_all_act ⟨i, hi_act, hy_nb⟩
        rw [hgy_f] at hgy_t
        exact Bool.false_ne_true hgy_t
      · rfl
  have htaps : ∀ L : List ↥H,
      ∃ (gs : List Gate) (f : ↥H → ℕ),
        WellFormed n gs ∧ notCountL gs = 1 ∧ Extends n gs3 gs ∧
        (∃ rest : List Gate, gs = gs2 ++ rest) ∧
        ∀ e ∈ L, f e < n + 2 + gs.length ∧
          ∀ x, cover x → wireVal n gs x (f e) = xor (x e.val.1) (x e.val.2) := by
    intro L
    induction L with
    | nil =>
      -- Show gs3 = gs2 ++ rest
      have hex_pref : ∀ (l1 l2 : List Gate), (∃ r1, resE.1 = gs2 ++ r1) → (∃ r2, gs3 = resE.1 ++ r2) →
          ∃ rest, gs3 = gs2 ++ rest := by
        rintro _ _ ⟨r1, h1⟩ ⟨r2, h2⟩; exact ⟨r1 ++ r2, by rw [h2, h1, List.append_assoc]⟩
      have haddEdge_pref : ∀ (es : List (Fin n × Fin n)) (gs : List Gate),
          ∃ rest, (addEdgeOrs n gs es).1 = gs ++ rest := by
        intro es
        induction es with
        | nil => intro gs; exact ⟨[], by simp [addEdgeOrs]⟩
        | cons e es ih =>
          intro gs
          rcases ih (gs ++ [⟨GateOp.or, [e.1.val, e.2.val]⟩]) with ⟨r, hr⟩
          exact ⟨⟨GateOp.or, [e.1.val, e.2.val]⟩ :: r, by dsimp only [addEdgeOrs]; rw [hr]; simp⟩
      have haddAnd_pref : ∀ (ws : List ℕ) (gs : List Gate),
          ∃ rest, (addAndList n gs ws).1 = gs ++ rest := by
        intro ws
        induction ws with
        | nil => intro gs; exact ⟨[], by simp [addAndList]⟩
        | cons w ws ih =>
          cases ws with
          | nil => intro gs; exact ⟨[], by simp [addAndList]⟩
          | cons w' ws' =>
            intro gs
            rcases ih gs with ⟨r, hr⟩
            exact ⟨r ++ [⟨GateOp.and, [w, (addAndList n gs (w' :: ws')).2]⟩], by
              dsimp only [addAndList]; rw [hr, List.append_assoc]⟩
      exact ⟨gs3, fun _ => 0, hwfC, hnc3, Extends.refl n gs3,
        hex_pref [] [] (haddEdge_pref G.toList gs2) (haddAnd_pref resE.2 resE.1),
        fun _ h => absurd h List.not_mem_nil⟩
    | cons e es ih =>
      rcases ih with ⟨gsA, fA, hwfA, hncA, hextA, ⟨restA, hprefA⟩, hfA⟩
      have hWA_lt : ∀ w ∈ W, w < n + 2 + gsA.length :=
        fun w hw => lt_of_lt_of_le (hW3_lt w hw) (by have := hextA.1; omega)
      have hmono_e : ∀ x y : Fin n → Bool, cover x → cover y →
          (∀ w ∈ W, wireVal n gsA x w ≤ wireVal n gsA y w) →
          xor (x e.val.1) (x e.val.2) ≤ xor (y e.val.1) (y e.val.2) := by
        intro x y hcx hcy hle
        apply hparity_mono e x y hcx hcy
        intro w hw
        have h := hle w hw
        rwa [hextA.2 x w (hW3_lt w hw), hextA.2 y w (hW3_lt w hw)] at h
      -- Build DNF explicitly so we keep initial segment property
      let D : List (Fin n → Bool) :=
        ((Finset.univ : Finset (Fin n → Bool)).filter
          (fun x => cover x ∧ xor (x e.val.1) (x e.val.2) = true)).toList
      have h1 := addTerms_spec n W D gsA hwfA hWA_lt
      set res1 := addTerms n gsA W D
      rcases h1 with ⟨hwf1', hnc1', hext1', hws1lt', hval1'⟩
      have h2 := addOrList_spec n res1.2 res1.1 hwf1' hws1lt'
      set res2 := addOrList n res1.1 res1.2
      rcases h2 with ⟨hwf2', hnc2', hext2', hw2lt', hval2'⟩
      have haddAnd_pref : ∀ (ws : List ℕ) (gs : List Gate),
          ∃ rest, (addAndList n gs ws).1 = gs ++ rest := by
        intro ws; induction ws with
        | nil => intro gs; exact ⟨[], by simp [addAndList]⟩
        | cons w ws ih =>
          cases ws with
          | nil => intro gs; exact ⟨[], by simp [addAndList]⟩
          | cons w' ws' =>
            intro gs; rcases ih gs with ⟨r, hr⟩
            exact ⟨r ++ [⟨GateOp.and, [w, (addAndList n gs (w' :: ws')).2]⟩], by
              dsimp only [addAndList]; rw [hr, List.append_assoc]⟩
      have haddOr_pref : ∀ (ws : List ℕ) (gs : List Gate),
          ∃ rest, (addOrList n gs ws).1 = gs ++ rest := by
        intro ws; induction ws with
        | nil => intro gs; exact ⟨[], by simp [addOrList]⟩
        | cons w ws ih =>
          cases ws with
          | nil => intro gs; exact ⟨[], by simp [addOrList]⟩
          | cons w' ws' =>
            intro gs; rcases ih gs with ⟨r, hr⟩
            exact ⟨r ++ [⟨GateOp.or, [w, (addOrList n gs (w' :: ws')).2]⟩], by
              dsimp only [addOrList]; rw [hr, List.append_assoc]⟩
      have haddTerms_pref : ∀ (Ds : List (Fin n → Bool)) (gs : List Gate),
          ∃ rest, (addTerms n gs W Ds).1 = gs ++ rest := by
        intro Ds; induction Ds with
        | nil => intro gs; exact ⟨[], by simp [addTerms]⟩
        | cons x0 xs ih =>
          intro gs
          rcases haddAnd_pref (W.filter (fun w => wireVal n gs x0 w)) gs with ⟨r1, hr1⟩
          rcases ih (addAndList n gs (W.filter (fun w => wireVal n gs x0 w))).1 with ⟨r2, hr2⟩
          exact ⟨r1 ++ r2, by dsimp only [addTerms]; rw [hr2, hr1, List.append_assoc]⟩
      rcases haddTerms_pref D gsA with ⟨rT, hrT⟩
      rcases haddOr_pref res1.2 res1.1 with ⟨rO, hrO⟩
      have hpref2 : ∃ rest, res2.1 = gs2 ++ rest :=
        ⟨restA ++ (rT ++ rO), by
          dsimp only [res2, res1]
          rw [hrO, hrT, hprefA, List.append_assoc, List.append_assoc]⟩
      have hwe_val : ∀ y : Fin n → Bool, cover y →
          wireVal n res2.1 y res2.2 = xor (y e.val.1) (y e.val.2) := by
        intro y hcy
        apply Bool.eq_iff_iff.mpr
        rw [hval2' y, hval1' y]
        constructor
        · rintro ⟨x₀, hx₀D, hle⟩
          have hx₀ := (Finset.mem_filter.mp (Finset.mem_toList.mp hx₀D)).2
          exact bool_true_le_eq (hx₀.2 ▸ hmono_e x₀ y hx₀.1 hcy hle)
        · intro hfy
          exact ⟨y, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hcy, hfy⟩),
            fun _ _ => le_rfl⟩
      refine ⟨res2.1, fun e' => if e' = e then res2.2 else fA e',
        hwf2', hnc2'.trans (hnc1'.trans hncA), hextA.trans (hext1'.trans hext2'), hpref2,
        fun e' he' => ?_⟩
      by_cases heq : e' = e
      · subst heq; simp only [↓reduceIte]; exact ⟨hw2lt', hwe_val⟩
      · simp only [heq, ↓reduceIte]
        rcases hfA e' ((List.mem_cons.mp he').resolve_left heq) with ⟨hflt, hfval⟩
        have hextA2 : Extends n gsA res2.1 := hext1'.trans hext2'
        refine ⟨lt_of_lt_of_le hflt (by have := hextA2.1; omega), fun x hx => ?_⟩
        rw [hextA2.2 x (fA e') hflt, hfval x hx]
  rcases htaps (Finset.univ : Finset ↥H).toList with ⟨gsF, fF, hwfF, hncF, hext3F, ⟨restF, hprefF⟩, hfF⟩
  let C : Circuit := ⟨gsF, wCov⟩
  have hwCovF : wCov < n + 2 + C.size := by
    change resC.2 < n + 2 + gsF.length
    have : resC.1.length ≤ gsF.length := hext3F.1
    omega
  have hnc_eq : PEqualNP.NotBracket.notCount C = 1 := by
    rw [← notCountL_eq_notCount C]; exact hncF
  have hj0_lt : j0 < C.gates.length := by
    change gs1.length < gsF.length
    rw [hprefF]; dsimp only [gs2]; simp
  have hext1F : Extends n gs1 gsF := hext12.trans (hext23.trans hext3F)
  refine ⟨C, ⟨hwfF.1, hwfF.2, hwCovF⟩,
    ⟨fun e => ⟨fF e, (hfF e (Finset.mem_toList.mpr (Finset.mem_univ e))).1⟩, fun x => ?_⟩,
    hnc_eq, ⟨j0, hj0_lt⟩, wg, ?_, ?_, ?_⟩
  · constructor
    · change wireVal n gsF x wCov = true ↔ cover x
      rw [hext3F.2 x wCov wCov_lt, hcov_spec x]
    · intro hcx e
      change wireVal n gsF x (fF e) = xor (x e.val.1) (x e.val.2)
      exact (hfF e (Finset.mem_toList.mpr (Finset.mem_univ e))).2 x hcx
  · simp only [List.get_eq_getElem]
    have hget : C.gates[j0] = gnot := by
      change gsF[gs1.length] = gnot
      simp only [hprefF, gs2]
      exact getElem_append_mid gs1 restF gnot
    rw [hget]
  · simp only [List.get_eq_getElem]
    have hget : C.gates[j0] = gnot := by
      change gsF[gs1.length] = gnot
      simp only [hprefF, gs2]
      exact getElem_append_mid gs1 restF gnot
    rw [hget]; rfl
  · intro x
    change wireVal n gsF x wg = g x
    rw [hext1F.2 x wg hwg_lt, hwg_val x trivial]

/-! ### Part 4: Conjunct 2 — Gate elimination for d outside sites and base case -/

def gateDeps (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

lemma wires_eq_of_no_dep_u {n : ℕ} (C : Circuit) (u : Fin n)
    (hno : ∀ g ∈ C.gates, u.val ∉ gateDeps g)
    (x y : Fin n → Bool) (hag : ∀ v : Fin n, v ≠ u → x v = y v) :
    ∀ w : ℕ, w ≠ u.val →
      (C.wires (List.ofFn x ++ [false, true])).getD w false =
      (C.wires (List.ofFn y ++ [false, true])).getD w false := by
  have hgen : ∀ (gs : List Gate) (wa wb : List Bool),
      (∀ g ∈ gs, u.val ∉ gateDeps g) →
      wa.length = wb.length → n + 2 ≤ wa.length →
      (∀ w, w ≠ u.val → wa.getD w false = wb.getD w false) →
      ∀ w, w ≠ u.val → (evalWires gs wa).getD w false = (evalWires gs wb).getD w false := by
    intro gs
    induction gs with
    | nil => intro wa wb _ _ _ hinv w hw; exact hinv w hw
    | cons g gs ih =>
      intro wa wb hno' hlen hge hinv
      have hgu : u.val ∉ gateDeps g := hno' g (List.mem_cons_self ..)
      have hveq : g.op.eval (g.inputs.map fun i => wa.getD i false) =
          g.op.eval (g.inputs.map fun i => wb.getD i false) := by
        cases hop : g.op with
        | not =>
          cases hin : g.inputs with
          | nil => rfl
          | cons k ks =>
            simp only [GateOp.eval, List.map_cons, List.headD_cons]
            have hku : k ≠ u.val := by
              intro h; apply hgu; simp [gateDeps, hop, hin, h]
            rw [hinv k hku]
        | and | or | mod _ | maj =>
          congr 1
          apply List.map_congr_left
          intro k hk
          have hku : k ≠ u.val := by
            intro h; apply hgu; simp [gateDeps, hop, h ▸ hk]
          exact hinv k hku
      apply ih _ _ (fun g' hg' => hno' g' (List.mem_cons_of_mem g hg'))
        (by simp [hlen]) (by simp; omega)
      intro w hw
      rw [getD_append_singleton, getD_append_singleton, hlen]
      by_cases h1 : w < wb.length
      · rw [if_pos h1, if_pos h1]; exact hinv w hw
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : w = wb.length
        · rw [if_pos h2, if_pos h2]; exact hveq
        · rw [if_neg h2, if_neg h2]
  apply hgen C.gates _ _ hno (by simp) (by simp)
  intro w hw
  by_cases hwn : w < n
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simp [hwn]), List.getElem?_append_left (by simp [hwn]),
        List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hwn, dif_pos hwn]
    have hne : (⟨w, hwn⟩ : Fin n) ≠ u := fun h => hw (congrArg Fin.val h)
    exact congrArg some (hag ⟨w, hwn⟩ hne) |> fun h => by simpa using h
  · have h1 : (List.ofFn x).length ≤ w := by simp; omega
    have h2 : (List.ofFn y).length ≤ w := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right h1, List.getElem?_append_right h2]
    simp

-- Fix input u to true and eliminate one non-NOT gate reading u.val
lemma eliminate_outside_site {n : ℕ} (G H : Finset (Fin n × Fin n))
    (hltG : ∀ e ∈ G, e.1 < e.2) (hHG : H ⊆ G) (hHne : H.Nonempty)
    (u v : Fin n) (hu_out : u ∉ H.image Prod.fst ∪ H.image Prod.snd)
    (huv : (u, v) ∈ G ∨ (v, u) ∈ G)
    (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size))
    (hfit : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (hout_lt : C.output < n + 2 + C.size)
    (hnc1 : PEqualNP.NotBracket.notCount C = 1)
    (hspec : ∀ x : Fin n → Bool,
      let wires := List.ofFn x ++ [false, true]
      (C.eval wires = true ↔ ∀ e ∈ G, x e.1 = true ∨ x e.2 = true) ∧
      ((∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        ∀ e, (C.wires wires).getD (tap e).val false = xor (x e.val.1) (x e.val.2))) :
    ∃ (C' : Circuit) (tap' : ↥H → Fin (n + 2 + C'.size)),
      C'.size + 1 = C.size ∧
      PEqualNP.MetaComplexity.FanInTwo C' ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C' ∧
      C'.output < n + 2 + C'.size ∧
      PEqualNP.NotBracket.notCount C' = 1 ∧
      ∀ x : Fin n → Bool,
        let wires := List.ofFn x ++ [false, true]
        (C'.eval wires = true ↔ ∀ e ∈ G.filter (fun e => e.1 ≠ u ∧ e.2 ≠ u), x e.1 = true ∨ x e.2 = true) ∧
        ((∀ e ∈ G.filter (fun e => e.1 ≠ u ∧ e.2 ≠ u), x e.1 = true ∨ x e.2 = true) →
          ∀ e, (C'.wires wires).getD (tap' e).val false = xor (x e.val.1) (x e.val.2)) := by
  let G' := G.filter (fun e => e.1 ≠ u ∧ e.2 ≠ u)
  have hne_uv : u ≠ v := by
    rcases huv with h | h
    · exact ne_of_lt (hltG (u, v) h)
    · exact (ne_of_lt (hltG (v, u) h)).symm
  -- First show C.output != u.val
  have hout_ne_u : C.output ≠ u.val := by
    intro heq
    let xu : Fin n → Bool := fun t => decide (t ≠ u)
    have hcov_u := cover_allExcept_singleton G hltG u
    have hev : C.eval (List.ofFn xu ++ [false, true]) = true := (hspec xu).1.mpr hcov_u
    have hval : C.eval (List.ofFn xu ++ [false, true]) = false := by
      dsimp only [Circuit.eval]
      rw [heq]
      change (evalWires C.gates (List.ofFn xu ++ [false, true])).getD u.val false = false
      rw [show C.gates = [] ++ C.gates by rfl,
          evalWires_getD_prefix [] C.gates _ u.val (by simp; have := u.isLt; omega)]
      change wireVal n [] xu u.val = false
      rw [wireVal_input_lt]; simp [xu]
    rw [hval] at hev; exact Bool.false_ne_true hev
  -- Next show some gate g in C.gates has u.val in gateDeps g
  have hex_dep : ∃ j : Fin C.gates.length, u.val ∈ gateDeps (C.gates.get j) := by
    by_contra hno
    push Not at hno
    have hno' : ∀ g ∈ C.gates, u.val ∉ gateDeps g := by
      intro g hg
      rcases List.mem_iff_get.mp hg with ⟨j, rfl⟩
      exact hno j
    let x1 : Fin n → Bool := fun t => decide (t ≠ v)
    let x0 : Fin n → Bool := fun t => decide (t ≠ u ∧ t ≠ v)
    have hag : ∀ t, t ≠ u → x0 t = x1 t := by intro t ht; simp [x0, x1, ht]
    have heq_out := wires_eq_of_no_dep_u C u hno' x0 x1 hag C.output hout_ne_u
    have hcov1 : ∀ e ∈ G, x1 e.1 = true ∨ x1 e.2 = true := cover_allExcept_singleton G hltG v
    have hncov0 : ¬ ∀ e ∈ G, x0 e.1 = true ∨ x0 e.2 = true := by
      intro hc
      rcases huv with h | h
      · rcases hc (u, v) h with h1 | h1 <;> simp [x0] at h1
      · rcases hc (v, u) h with h1 | h1 <;> simp [x0] at h1
    have hev1 : C.eval (List.ofFn x1 ++ [false, true]) = true := (hspec x1).1.mpr hcov1
    have hev0 : C.eval (List.ofFn x0 ++ [false, true]) = false := by
      cases h : C.eval (List.ofFn x0 ++ [false, true])
      · rfl
      · exact absurd ((hspec x0).1.mp h) hncov0
    dsimp only [Circuit.eval] at hev0 hev1
    rw [heq_out, hev1] at hev0
    exact Bool.false_ne_true hev0.symm
  rcases hex_dep with ⟨jStar, hjStar_dep⟩
  let gStar := C.gates.get jStar
  change u.val ∈ gateDeps gStar at hjStar_dep
  -- Show gStar is NOT a NOT gate!
  have hgStar_ne_not : gStar.op ≠ GateOp.not := by
    intro hnot_op
    have hhead : gStar.inputs.head? = some u.val := by
      dsimp only [gateDeps] at hjStar_dep
      rw [hnot_op] at hjStar_dep
      cases hin : gStar.inputs with
      | nil => rw [hin] at hjStar_dep; simp at hjStar_dep
      | cons a as =>
        rw [hin] at hjStar_dep
        simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hjStar_dep
        simp [hjStar_dep]
    have hncL : notCountL C.gates = 1 := (notCountL_eq_notCount C).trans hnc1
    rcases split_unique_not C.gates hncL with ⟨pre, post, g0, hgs_eq, hg0_op, hpre0, hpost0⟩
    have hj_val : jStar.val = pre.length := by
      have hj' : ((pre ++ [g0] ++ post).get ⟨jStar.val, hgs_eq ▸ jStar.isLt⟩).op = GateOp.not := by
        simpa [gStar, List.get_eq_getElem, hgs_eq] using hnot_op
      exact unique_not_index_eq hpre0 hpost0 ⟨jStar.val, hgs_eq ▸ jStar.isLt⟩ hj'
    have hg0_eq : gStar = g0 := by
      dsimp only [gStar]; simp only [List.get_eq_getElem]
      have h1 : C.gates[jStar.val] = (pre ++ [g0] ++ post)[pre.length]'(by simp) := by
        simp only [hgs_eq, hj_val]
      rw [h1, getElem_append_mid]
    rw [hg0_eq] at hhead
    rcases one_not_guard_step C hfit hrb hnc1 pre post g0 hgs_eq hg0_op hpre0 hpost0 u.val hhead with
      ⟨_, _, hmono_wires⟩
    rcases hHne with ⟨e0, he0H⟩
    have hu_ne1 : u ≠ e0.1 := fun h =>
      hu_out (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e0, he0H, h.symm⟩))
    let x1 : Fin n → Bool := fun t => decide (t ≠ e0.1)
    let xT : Fin n → Bool := fun _ => true
    have hgu_eq : (C.wires (List.ofFn x1 ++ [false, true])).getD u.val false =
        (C.wires (List.ofFn xT ++ [false, true])).getD u.val false := by
      have hpre1 : ∀ x : Fin n → Bool,
          (C.wires (List.ofFn x ++ [false, true])).getD u.val false = x u := by
        intro x
        change (evalWires ([] ++ C.gates) _).getD u.val false = _
        rw [evalWires_getD_prefix [] C.gates _ u.val (by simp; have := u.isLt; omega)]
        exact wireVal_input_lt x u
      rw [hpre1 x1, hpre1 xT]; simp [x1, xT, hu_ne1]
    have hle := hmono_wires x1 xT (fun _ _ => rfl) hgu_eq (tap ⟨e0, he0H⟩).val
    have hcov1 := cover_allExcept_singleton G hltG e0.1
    have hcovT : ∀ e ∈ G, xT e.1 = true ∨ xT e.2 = true := fun _ _ => Or.inl rfl
    have hne_e0 : e0.1 ≠ e0.2 := ne_of_lt (hltG e0 (hHG he0H))
    rw [(hspec x1).2 hcov1 ⟨e0, he0H⟩, (hspec xT).2 hcovT ⟨e0, he0H⟩] at hle
    simp [x1, xT, hne_e0.symm] at hle
    exact absurd hle (by decide)
  -- Since gStar is AND or OR and has u.val in gStar.inputs, find replacement wire r < n + 2 + jStar.val
  have hgStar_fit := hfit gStar (List.get_mem C.gates jStar)
  have hgStar_op : gStar.op = GateOp.and ∨ gStar.op = GateOp.or := by
    have hm := hgStar_fit.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hgStar_ne_not
  have hu_in : u.val ∈ gStar.inputs := by
    rcases hgStar_op with h | h <;> simpa [gateDeps, h] using hjStar_dep
  have hrb_star : ∀ i ∈ gStar.inputs, i < n + 2 + jStar.val := by
    have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C jStar.val = gStar := by
      dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt, gStar]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem jStar.isLt]; rfl
    exact fun i hi => hrb jStar.val jStar.isLt i (hgat ▸ hi)
  -- Replacement wire r (before remapping): either n + 1 (true) or the other input y of AND
  let replWire : GateOp → List ℕ → ℕ
    | GateOp.and, [a, b] => if a = u.val then (if b = u.val then n + 1 else b) else a
    | _, _ => n + 1
  let r0 : ℕ := replWire gStar.op gStar.inputs
  have hr0_lt : r0 < n + 2 + jStar.val := by
    dsimp only [r0]
    cases hop : gStar.op with
    | and =>
      cases hin : gStar.inputs with
      | nil => dsimp only [replWire]; omega
      | cons a tl =>
        cases tl with
        | nil => dsimp only [replWire]; omega
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            dsimp only [replWire]
            have ha : a < n + 2 + jStar.val := hrb_star a (by rw [hin]; simp)
            have hb : b < n + 2 + jStar.val := hrb_star b (by rw [hin]; simp)
            split_ifs <;> omega
          | cons _ _ => dsimp only [replWire]; omega
    | or | not | mod _ | maj => dsimp only [replWire]; omega
  have hr0_ne_u : r0 ≠ u.val := by
    dsimp only [r0]
    cases hop : gStar.op with
    | and =>
      cases hin : gStar.inputs with
      | nil => dsimp only [replWire]; have := u.isLt; omega
      | cons a tl =>
        cases tl with
        | nil => dsimp only [replWire]; have := u.isLt; omega
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            dsimp only [replWire]
            split_ifs with h1 h2
            · have := u.isLt; omega
            · exact h2
            · exact h1
          | cons _ _ => dsimp only [replWire]; have := u.isLt; omega
    | or | not | mod _ | maj => dsimp only [replWire]; have := u.isLt; omega
  have hr0_eval : ∀ ws : List Bool, ws.length = n + 2 + jStar.val →
      ws.getD u.val false = true → ws.getD (n + 1) false = true →
      gStar.op.eval (gStar.inputs.map fun i => ws.getD i false) = ws.getD r0 false := by
    intro ws hlen hwu hwt
    have hlen2 : gStar.inputs.length ≤ 2 := hgStar_fit.2
    rcases hgStar_op with hop | hop
    · cases hin : gStar.inputs with
      | nil => rw [hin] at hu_in; simp at hu_in
      | cons a tl =>
        cases tl with
        | nil =>
          rw [hin] at hu_in; simp at hu_in; subst hu_in
          dsimp only [r0]; rw [hop, hin]; dsimp only [replWire]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true]
          rw [hwu, hwt]
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            rw [hin] at hu_in; simp at hu_in
            dsimp only [r0]; rw [hop, hin]; dsimp only [replWire]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true]
            by_cases ha : a = u.val
            · subst ha
              rw [if_pos rfl]
              by_cases hb : b = u.val
              · subst hb; rw [if_pos rfl, hwu, hwt]; rfl
              · rw [if_neg hb, hwu, Bool.true_and]
            · have hb : b = u.val := (hu_in.resolve_left (Ne.symm ha)).symm
              subst hb; rw [if_neg ha, hwu, Bool.and_true]
          | cons _ _ => rw [hin] at hlen2; simp at hlen2
    · cases hin : gStar.inputs with
      | nil => rw [hin] at hu_in; simp at hu_in
      | cons a tl =>
        cases tl with
        | nil =>
          rw [hin] at hu_in; simp at hu_in; subst hu_in
          dsimp only [r0]; rw [hop, hin]; dsimp only [replWire]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false]
          rw [hwu, hwt]
        | cons b tl2 =>
          cases tl2 with
          | nil =>
            rw [hin] at hu_in; simp at hu_in
            dsimp only [r0]; rw [hop, hin]; dsimp only [replWire]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false]
            rcases hu_in with rfl | rfl
            · rw [hwu, hwt, Bool.true_or]
            · rw [hwu, hwt, Bool.or_true]
          | cons _ _ => rw [hin] at hlen2; simp at hlen2
  -- Define remap and new circuit C' by removing gate jStar and remapping wires
  let remap : ℕ → ℕ := fun w =>
    if w < n + 2 + jStar.val then (if w = u.val then n + 1 else w)
    else if w = n + 2 + jStar.val then r0
    else w - 1
  let mapGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map remap⟩
  let gsPre := C.gates.take jStar.val
  let gsPost := C.gates.drop (jStar.val + 1)
  have hC_split : C.gates = gsPre ++ [gStar] ++ gsPost := by
    have h1 := List.take_append_drop jStar.val C.gates
    have h2 : C.gates.drop jStar.val = gStar :: gsPost := by
      dsimp only [gStar, gsPost]
      rw [List.drop_eq_getElem_cons jStar.isLt]; rfl
    rw [← h1, h2]; simp [gsPre]
  have hpre_len : gsPre.length = jStar.val := List.length_take_of_le (le_of_lt jStar.isLt)
  have hC_len_split : C.gates.length = gsPre.length + 1 + gsPost.length := by
    have := congrArg List.length hC_split
    simp only [List.length_append, List.length_singleton] at this
    exact this
  let gs' : List Gate := gsPre.map mapGate ++ gsPost.map mapGate
  let C' : Circuit := ⟨gs', remap C.output⟩
  have hC'_size : C'.size + 1 = C.size := by
    change (gsPre.map mapGate ++ gsPost.map mapGate).length + 1 = C.gates.length
    simp only [List.length_append, List.length_map]
    omega
  have hremap_lt : ∀ w, w < n + 2 + C.size → remap w < n + 2 + C'.size := by
    intro w hw
    have hjlt : jStar.val < C.size := jStar.isLt
    have hrlt := hr0_lt
    dsimp only [remap]
    split_ifs <;> omega
  have hfit' : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    dsimp only [C', gs'] at hg
    rcases List.mem_append.mp hg with h1 | h2
    · rcases List.mem_map.mp h1 with ⟨g0, hg0, rfl⟩
      have hf := hfit g0 (List.mem_of_mem_take hg0)
      exact ⟨hf.1, by simp [mapGate, hf.2]⟩
    · rcases List.mem_map.mp h2 with ⟨g0, hg0, rfl⟩
      have hf := hfit g0 (List.mem_of_mem_drop hg0)
      exact ⟨hf.1, by simp [mapGate, hf.2]⟩
  have hrb' : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C' := by
    intro j hj i hi
    have hj_len : j < gsPre.length + gsPost.length := by simpa [C', gs'] using hj
    dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt, C', gs'] at hi
    by_cases hlt : j < gsPre.length
    · have hget : (gsPre.map mapGate ++ gsPost.map mapGate).getD j ⟨GateOp.or, []⟩ =
          mapGate (C.gates.getD j ⟨GateOp.or, []⟩) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlt]),
            List.getElem?_map, List.getElem?_take_of_lt (by omega),
            List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by omega)]
        rfl
      rw [hget] at hi
      rcases List.mem_map.mp hi with ⟨k, hk, rfl⟩
      have hk_lt : k < n + 2 + j := hrb j (by omega) k hk
      dsimp only [remap]
      rw [if_pos (by omega)]
      split_ifs <;> omega
    · have hge : gsPre.length ≤ j := Nat.le_of_not_lt hlt
      have hget : (gsPre.map mapGate ++ gsPost.map mapGate).getD j ⟨GateOp.or, []⟩ =
          mapGate (C.gates.getD (j + 1) ⟨GateOp.or, []⟩) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hge]),
            List.length_map, List.getElem?_map, List.getElem?_drop,
            List.getD_eq_getElem?_getD]
        have hidx : jStar.val + 1 + (j - gsPre.length) = j + 1 := by omega
        rw [hidx, List.getElem?_eq_getElem (by omega)]
        rfl
      rw [hget] at hi
      rcases List.mem_map.mp hi with ⟨k, hk, rfl⟩
      have hk_lt : k < n + 2 + (j + 1) := hrb (j + 1) (by omega) k hk
      dsimp only [remap]
      split_ifs <;> omega
  have hnc' : PEqualNP.NotBracket.notCount C' = 1 := by
    rw [← notCountL_eq_notCount C']
    have hncL : notCountL C.gates = 1 := (notCountL_eq_notCount C).trans hnc1
    have hmap_nc : ∀ l : List Gate, notCountL (l.map mapGate) = notCountL l := by
      intro l; induction l with
      | nil => rfl
      | cons g l ih =>
        simp only [List.map_cons, notCountL, List.filter_cons, mapGate]
        cases isNotOp g.op <;> simp [notCountL] at ih ⊢ <;> omega
    change notCountL (gsPre.map mapGate ++ gsPost.map mapGate) = 1
    rw [notCountL_append, hmap_nc, hmap_nc]
    rw [hC_split, notCountL_append, notCountL_append] at hncL
    have hstar0 : notCountL [gStar] = 0 := by
      have : isNotOp gStar.op = false := by
        cases h : gStar.op with
        | not => exact absurd h hgStar_ne_not
        | and | or | mod _ | maj => rfl
      simp [notCountL, this]
    omega
  -- Semantic simulation: for every x, wireVal C' x (remap w) = wireVal C (update x u true) w
  have hsim : ∀ x : Fin n → Bool,
      ∀ w < n + 2 + C.size,
        (C'.wires (List.ofFn x ++ [false, true])).getD (remap w) false =
        (C.wires (List.ofFn (Function.update x u true) ++ [false, true])).getD w false := by
    intro x
    let x' := Function.update x u true
    let inp := List.ofFn x ++ [false, true]
    let inp' := List.ofFn x' ++ [false, true]
    -- Phase 1: simulate gsPre
    have hpre_sim : ∀ (k : ℕ) (hk : k ≤ gsPre.length),
        ∀ w < n + 2 + k,
          (evalWires ((gsPre.take k).map mapGate) inp).getD (remap w) false =
          (evalWires (gsPre.take k) inp').getD w false := by
      intro k
      induction k with
      | zero =>
        intro _ w hw
        simp only [List.take_zero, List.map_nil, evalWires, List.foldl_nil]
        have hlt_star : w < n + 2 + jStar.val := by omega
        dsimp only [remap]; rw [if_pos hlt_star]
        by_cases hwu : w = u.val
        · subst hwu
          rw [if_pos rfl]
          have h1 : inp.getD (n + 1) false = true := wireVal_const_true x
          have h2 : inp'.getD u.val false = x' u := wireVal_input_lt x' u
          rw [h1, h2]; simp [x']
        · rw [if_neg hwu]
          by_cases hwn : w < n
          · have h1 : inp.getD w false = x ⟨w, hwn⟩ := wireVal_input_lt x ⟨w, hwn⟩
            have h2 : inp'.getD w false = x' ⟨w, hwn⟩ := wireVal_input_lt x' ⟨w, hwn⟩
            rw [h1, h2]
            have hne : (⟨w, hwn⟩ : Fin n) ≠ u := fun h => hwu (congrArg Fin.val h)
            simp [x', Function.update_of_ne hne]
          · have hge1 : (List.ofFn x).length ≤ w := by simp; omega
            have hge2 : (List.ofFn x').length ≤ w := by simp; omega
            dsimp only [inp, inp']
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_append_right hge1, List.getElem?_append_right hge2]
            simp
      | succ k ih =>
        intro hk w hw
        have hkt : k < C.gates.length := by omega
        have htake : gsPre.take (k + 1) = gsPre.take k ++ [C.gates[k]] := by
          rw [List.take_add_one, List.getElem?_take_of_lt (by omega),
              List.getElem?_eq_getElem hkt]; rfl
        rw [htake, List.map_append, List.map_singleton, evalWires_append, evalWires_append]
        set ws1 := evalWires ((gsPre.take k).map mapGate) inp
        set ws2 := evalWires (gsPre.take k) inp'
        have hl1 : ws1.length = n + 2 + k := by
          dsimp only [ws1, inp]; rw [evalWires_length, List.length_map, List.length_take_of_le (by omega)]; simp
        have hl2 : ws2.length = n + 2 + k := by
          dsimp only [ws2, inp']; rw [evalWires_length, List.length_take_of_le (by omega)]; simp
        let gk := C.gates[k]
        change (ws1 ++ [(mapGate gk).op.eval ((mapGate gk).inputs.map fun i => ws1.getD i false)]).getD (remap w) false =
          (ws2 ++ [gk.op.eval (gk.inputs.map fun i => ws2.getD i false)]).getD w false
        by_cases hw_lt : w < n + 2 + k
        · have hrm_lt : remap w < n + 2 + k := by
            dsimp only [remap]; rw [if_pos (by omega)]; split_ifs <;> omega
          rw [getD_append_singleton, if_pos (by omega), getD_append_singleton, if_pos (by omega)]
          exact ih (by omega) w hw_lt
        · have hweq : w = n + 2 + k := by omega
          have hrm_eq : remap w = n + 2 + k := by
            dsimp only [remap]; rw [if_pos (by omega), if_neg (by have := u.isLt; omega)]; exact hweq
          rw [hrm_eq, hweq, getD_append_singleton, if_neg (by omega), if_pos hl1.symm,
              getD_append_singleton, if_neg (by omega), if_pos hl2.symm]
          dsimp only [mapGate]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro i hi
          have hi_lt : i < n + 2 + k := by
            have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C k = gk := by
              dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt, gk]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkt]; rfl
            exact hrb k hkt i (hgat ▸ hi)
          exact ih (by omega) i hi_lt
    -- Phase 2: simulate gsPost
    have hpost_sim : ∀ (k : ℕ) (hk : k ≤ gsPost.length),
        ∀ w < n + 2 + jStar.val + 1 + k,
          (evalWires (gsPre.map mapGate ++ (gsPost.take k).map mapGate) inp).getD (remap w) false =
          (evalWires (gsPre ++ [gStar] ++ gsPost.take k) inp').getD w false := by
      intro k
      induction k with
      | zero =>
        intro _ w hw
        simp only [List.take_zero, List.map_nil, List.append_nil]
        set ws1 := evalWires (gsPre.map mapGate) inp
        set ws2 := evalWires gsPre inp'
        have hl1 : ws1.length = n + 2 + jStar.val := by
          dsimp only [ws1, inp]; rw [evalWires_length, List.length_map, hpre_len]; simp
        have hl2 : ws2.length = n + 2 + jStar.val := by
          dsimp only [ws2, inp']; rw [evalWires_length, hpre_len]; simp
        have hpre_full : ∀ z < n + 2 + jStar.val, ws1.getD (remap z) false = ws2.getD z false := by
          intro z hz
          have h := hpre_sim gsPre.length le_rfl z (by omega)
          rwa [List.take_length] at h
        rw [evalWires_append]
        change ws1.getD (remap w) false =
          (ws2 ++ [gStar.op.eval (gStar.inputs.map fun i => ws2.getD i false)]).getD w false
        by_cases hlt : w < n + 2 + jStar.val
        · rw [getD_append_singleton, if_pos (by omega)]
          exact hpre_full w hlt
        · have hweq : w = n + 2 + jStar.val := by omega
          rw [hweq, getD_append_singleton, if_neg (by omega), if_pos hl2.symm]
          have hrm : remap (n + 2 + jStar.val) = r0 := by
            dsimp only [remap]; rw [if_neg (lt_irrefl _), if_pos rfl]
          have hrm_r0 : remap r0 = r0 := by
            dsimp only [remap]; rw [if_pos hr0_lt, if_neg hr0_ne_u]
          rw [hrm, ← hrm_r0, hpre_full r0 hr0_lt]
          have hwu : ws2.getD u.val false = true := by
            dsimp only [ws2]
            rw [show gsPre = [] ++ gsPre by rfl,
                evalWires_getD_prefix [] gsPre inp' u.val (by simp [inp']; have := u.isLt; omega)]
            have h := wireVal_input_lt x' u; simp [x'] at h; exact h
          have hwt : ws2.getD (n + 1) false = true := by
            dsimp only [ws2]
            rw [show gsPre = [] ++ gsPre by rfl,
                evalWires_getD_prefix [] gsPre inp' (n + 1) (by simp [inp'])]
            exact wireVal_const_true x'
          exact (hr0_eval ws2 hl2 hwu hwt).symm
      | succ k ih =>
        intro hk w hw
        have hidx_lt : jStar.val + 1 + k < C.gates.length := by omega
        let gk := C.gates[jStar.val + 1 + k]
        have htake : gsPost.take (k + 1) = gsPost.take k ++ [gk] := by
          rw [List.take_add_one]
          dsimp only [gsPost, gk]
          rw [List.getElem?_drop, List.getElem?_eq_getElem hidx_lt]; rfl
        rw [htake, List.map_append, List.map_singleton]
        rw [show gsPre.map mapGate ++ ((gsPost.take k).map mapGate ++ [mapGate gk]) =
              (gsPre.map mapGate ++ (gsPost.take k).map mapGate) ++ [mapGate gk] by simp [List.append_assoc]]
        rw [show gsPre ++ [gStar] ++ (gsPost.take k ++ [gk]) =
              (gsPre ++ [gStar] ++ gsPost.take k) ++ [gk] by simp [List.append_assoc]]
        rw [evalWires_append (gsPre.map mapGate ++ (gsPost.take k).map mapGate) [mapGate gk] inp,
            evalWires_append (gsPre ++ [gStar] ++ gsPost.take k) [gk] inp']
        set ws1 := evalWires (gsPre.map mapGate ++ (gsPost.take k).map mapGate) inp
        set ws2 := evalWires (gsPre ++ [gStar] ++ gsPost.take k) inp'
        have hl1 : ws1.length = n + 2 + jStar.val + k := by
          simp only [ws1, inp, evalWires_length, List.length_append, List.length_map, List.length_ofFn,
            List.length_cons, List.length_nil, hpre_len, List.length_take_of_le (by omega : k ≤ gsPost.length)]
          omega
        have hl2 : ws2.length = n + 2 + jStar.val + 1 + k := by
          simp only [ws2, inp', evalWires_length, List.length_append, List.length_ofFn,
            List.length_cons, List.length_nil, hpre_len, List.length_take_of_le (by omega : k ≤ gsPost.length)]
          omega
        change (ws1 ++ [(mapGate gk).op.eval ((mapGate gk).inputs.map fun i => ws1.getD i false)]).getD (remap w) false =
          (ws2 ++ [gk.op.eval (gk.inputs.map fun i => ws2.getD i false)]).getD w false
        by_cases hw_lt : w < n + 2 + jStar.val + 1 + k
        · have hrm_lt : remap w < n + 2 + jStar.val + k := by
            dsimp only [remap]; split_ifs <;> omega
          rw [getD_append_singleton, if_pos (by omega), getD_append_singleton, if_pos (by omega)]
          exact ih (by omega) w hw_lt
        · have hweq : w = n + 2 + jStar.val + 1 + k := by omega
          have hrm_eq : remap w = n + 2 + jStar.val + k := by
            dsimp only [remap]; rw [if_neg (by omega), if_neg (by omega)]; omega
          rw [hrm_eq, hweq, getD_append_singleton, if_neg (by omega), if_pos hl1.symm,
              getD_append_singleton, if_neg (by omega), if_pos hl2.symm]
          dsimp only [mapGate]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro i hi
          have hi_lt : i < n + 2 + jStar.val + 1 + k := by
            have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C (jStar.val + 1 + k) = gk := by
              dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt, gk]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt]; rfl
            have := hrb (jStar.val + 1 + k) hidx_lt i (hgat ▸ hi); omega
          exact ih (by omega) i hi_lt
    intro w hw
    have hfin := hpost_sim gsPost.length le_rfl w (by
      change w < n + 2 + C.gates.length at hw; omega)
    rw [List.take_length] at hfin
    rw [← hC_split] at hfin
    exact hfin
  -- Package C' and tap'
  let tap' : ↥H → Fin (n + 2 + C'.size) := fun e => ⟨remap (tap e).val, hremap_lt _ (tap e).isLt⟩
  refine ⟨C', tap', hC'_size, hfit', hrb', hremap_lt _ hout_lt, hnc', fun x => ?_⟩
  let x' := Function.update x u true
  have hcov_iff : (∀ e ∈ G', x e.1 = true ∨ x e.2 = true) ↔
      (∀ e ∈ G, x' e.1 = true ∨ x' e.2 = true) := by
    constructor
    · intro hc e he
      by_cases h1 : e.1 = u
      · left; simp [x', h1]
      · by_cases h2 : e.2 = u
        · right; simp [x', h2]
        · simp only [x', Function.update_of_ne h1, Function.update_of_ne h2]
          exact hc e (Finset.mem_filter.mpr ⟨he, h1, h2⟩)
    · intro hc e he
      rcases Finset.mem_filter.mp he with ⟨heG, h1, h2⟩
      simpa [x', Function.update_of_ne h1, Function.update_of_ne h2] using hc e heG
  constructor
  · dsimp only [Circuit.eval, C']
    rw [hsim x C.output hout_lt]
    exact ((hspec x').1).trans hcov_iff.symm
  · intro hcx e
    dsimp only [tap']
    rw [hsim x (tap e).val (tap e).isLt, (hspec x').2 (hcov_iff.mp hcx) e]
    have h1ne : e.val.1 ≠ u := fun h =>
      hu_out (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e.val, e.property, h⟩))
    have h2ne : e.val.2 ≠ u := fun h =>
      hu_out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.val, e.property, h⟩))
    simp [x', Function.update_of_ne h1ne, Function.update_of_ne h2ne]

/-! ### Part 5: Base case (d = 0) via exact cone expansion -/

def expand (n : ℕ) (pre : List Gate) : ℕ → Finset ℕ → Finset ℕ × Finset ℕ
  | 0, S => (S, ∅)
  | k + 1, S =>
    if n + 2 + k ∈ S then
      let g := pre.getD k ⟨GateOp.or, []⟩
      let res := expand n pre k ((S.erase (n + 2 + k)) ∪ g.inputs.toFinset)
      (res.1, insert k res.2)
    else
      expand n pre k S

lemma expand_subset_range (n : ℕ) (pre : List Gate) :
    ∀ (m : ℕ) (T : Finset ℕ), (expand n pre m T).2 ⊆ Finset.range m
  | 0, _ => by simp [expand]
  | m + 1, T => by
    dsimp only [expand]
    split_ifs
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxm | hx'
      · rw [hxm]; exact Finset.mem_range.mpr (Nat.lt_succ_self m)
      · exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp (expand_subset_range n pre m _ hx')) (Nat.lt_succ_self m))
    · intro x hx
      exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp (expand_subset_range n pre m _ hx)) (Nat.lt_succ_self m))

lemma expand_basic (n : ℕ) (pre : List Gate)
    (hlen : ∀ j < pre.length, (pre.getD j ⟨GateOp.or, []⟩).inputs.length ≤ 2)
    (hrb : ∀ j < pre.length, ∀ i ∈ (pre.getD j ⟨GateOp.or, []⟩).inputs, i < n + 2 + j) :
    ∀ (k : ℕ), k ≤ pre.length → ∀ S : Finset ℕ, (∀ w ∈ S, w < n + 2 + k) →
      let res := expand n pre k S
      (∀ w ∈ res.1, w < n + 2) ∧
      res.2 ⊆ Finset.range k ∧
      res.1.card ≤ S.card + res.2.card := by
  intro k
  induction k with
  | zero =>
    intro _ S hS
    dsimp only [expand]
    exact ⟨hS, Finset.empty_subset _, by simp⟩
  | succ k ih =>
    intro hk S hS
    dsimp only [expand]
    by_cases hmem : n + 2 + k ∈ S
    · rw [if_pos hmem]
      set g := pre.getD k ⟨GateOp.or, []⟩
      set S' := (S.erase (n + 2 + k)) ∪ g.inputs.toFinset
      have hS' : ∀ w ∈ S', w < n + 2 + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with h1 | h2
        · have hne := (Finset.mem_erase.mp h1).1
          have hlt := hS w (Finset.mem_erase.mp h1).2
          omega
        · exact hrb k (by omega) w (List.mem_toFinset.mp h2)
      rcases ih (by omega) S' hS' with ⟨hL, hK, hcard⟩
      have hk_not : k ∉ (expand n pre k S').2 := fun h => by
        have := Finset.mem_range.mp (hK h); omega
      have hS'card : S'.card ≤ S.card + 1 := by
        have h1 : S'.card ≤ (S.erase (n + 2 + k)).card + g.inputs.toFinset.card :=
          Finset.card_union_le _ _
        have h2 : (S.erase (n + 2 + k)).card = S.card - 1 := Finset.card_erase_of_mem hmem
        have h3 : g.inputs.toFinset.card ≤ 2 :=
          le_trans (List.toFinset_card_le _) (hlen k (by omega))
        have h4 : 1 ≤ S.card := Finset.card_pos.mpr ⟨n + 2 + k, hmem⟩
        omega
      refine ⟨hL, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp (hK hj')) (Nat.lt_succ_self k))
      · change (expand n pre k S').1.card ≤ S.card + (insert k (expand n pre k S').2).card
        rw [Finset.card_insert_of_notMem hk_not]; omega
    · rw [if_neg hmem]
      have hS' : ∀ w ∈ S, w < n + 2 + k := by
        intro w hw
        have hlt := hS w hw
        have hne : w ≠ n + 2 + k := fun h => hmem (h ▸ hw)
        omega
      rcases ih (by omega) S hS' with ⟨hL, hK, hcard⟩
      refine ⟨hL, fun j hj => Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp (hK hj)) (Nat.lt_succ_self k)), hcard⟩

lemma expand_agree (n : ℕ) (pre : List Gate)
    (hrb : ∀ j < pre.length, ∀ i ∈ (pre.getD j ⟨GateOp.or, []⟩).inputs, i < n + 2 + j)
    (x y : Fin n → Bool) :
    ∀ (k : ℕ), k ≤ pre.length → ∀ S : Finset ℕ, (∀ w ∈ S, w < n + 2 + k) →
      (∀ u : Fin n, u.val ∈ (expand n pre k S).1 → x u = y u) →
      ∀ w ∈ S, wireVal n (pre.take k) x w = wireVal n (pre.take k) y w := by
  intro k
  induction k with
  | zero =>
    intro _ S hS hag w hw
    dsimp only [expand] at hag
    simp only [List.take_zero]
    by_cases hwn : w < n
    · rw [wireVal_input_lt x ⟨w, hwn⟩, wireVal_input_lt y ⟨w, hwn⟩]
      exact hag ⟨w, hwn⟩ hw
    · have hlt := hS w hw
      have : w = n ∨ w = n + 1 := by omega
      rcases this with rfl | rfl
      · rw [wireVal_const_false, wireVal_const_false]
      · rw [wireVal_const_true, wireVal_const_true]
  | succ k ih =>
    intro hk S hS hag
    have htake : pre.take (k + 1) = pre.take k ++ [pre.getD k ⟨GateOp.or, []⟩] :=
      take_succ_eq_getD pre (by omega)
    have hlen_take : (pre.take k).length = k := List.length_take_of_le (by omega)
    let gk := pre.getD k ⟨GateOp.or, []⟩
    dsimp only [expand] at hag
    by_cases hmem : n + 2 + k ∈ S
    · rw [if_pos hmem] at hag
      let S' := (S.erase (n + 2 + k)) ∪ gk.inputs.toFinset
      have hS' : ∀ w ∈ S', w < n + 2 + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with h1 | h2
        · have := (Finset.mem_erase.mp h1).1; have := hS w (Finset.mem_erase.mp h1).2; omega
        · exact hrb k (by omega) w (List.mem_toFinset.mp h2)
      have hih := ih (by omega) S' hS' hag
      intro w hw
      rw [htake]
      by_cases hwk : w = n + 2 + k
      · subst hwk
        have hpx := wireVal_push_new (pre.take k) gk x
        have hpy := wireVal_push_new (pre.take k) gk y
        rw [hlen_take] at hpx hpy
        rw [hpx, hpy]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hih i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
      · have hw_lt : w < n + 2 + k := by have := hS w hw; omega
        have hext : Extends n (pre.take k) (pre.take k ++ [gk]) := extends_push _ _
        rw [hext.2 x w (by omega), hext.2 y w (by omega)]
        exact hih w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hw⟩))
    · rw [if_neg hmem] at hag
      have hS' : ∀ w ∈ S, w < n + 2 + k := by
        intro w hw; have := hS w hw; have : w ≠ n + 2 + k := fun h => hmem (h ▸ hw); omega
      have hih := ih (by omega) S hS' hag
      intro w hw
      rw [htake]
      have hext : Extends n (pre.take k) (pre.take k ++ [gk]) := extends_push _ _
      rw [hext.2 x w (by have := hS' w hw; omega), hext.2 y w (by have := hS' w hw; omega)]
      exact hih w hw

lemma expand_partition_eq (n : ℕ) (pre : List Gate)
    (hlen : ∀ j < pre.length, (pre.getD j ⟨GateOp.or, []⟩).inputs.length ≤ 2)
    (hrb : ∀ j < pre.length, ∀ i ∈ (pre.getD j ⟨GateOp.or, []⟩).inputs, i < n + 2 + j) :
    ∀ (k : ℕ), k ≤ pre.length → ∀ (A B : Finset ℕ),
      (∀ w ∈ A ∪ B, w < n + 2 + k) → Disjoint A B →
      (expand n pre k (A ∪ B)).1.card = (A ∪ B).card + (expand n pre k (A ∪ B)).2.card →
      Disjoint (expand n pre k A).1 (expand n pre k B).1 ∧
      (expand n pre k A).1.card = A.card + (expand n pre k A).2.card ∧
      (expand n pre k B).1.card = B.card + (expand n pre k B).2.card ∧
      (expand n pre k (A ∪ B)).1 = (expand n pre k A).1 ∪ (expand n pre k B).1 := by
  intro k
  induction k with
  | zero =>
    intro _ A B _ hdisj _
    dsimp only [expand]
    exact ⟨hdisj, by simp, by simp, rfl⟩
  | succ k ih =>
    intro hk A B hAB hdisj heq
    set S := A ∪ B
    have hS : ∀ w ∈ S, w < n + 2 + (k + 1) := hAB
    dsimp only [expand] at heq ⊢
    by_cases hmem : n + 2 + k ∈ S
    · rw [if_pos hmem] at heq
      set g := pre.getD k ⟨GateOp.or, []⟩
      set S' := (S.erase (n + 2 + k)) ∪ g.inputs.toFinset
      have hS' : ∀ w ∈ S', w < n + 2 + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with h1 | h2
        · have := (Finset.mem_erase.mp h1).1; have := hS w (Finset.mem_erase.mp h1).2; omega
        · exact hrb k (by omega) w (List.mem_toFinset.mp h2)
      rcases expand_basic n pre hlen hrb k (by omega) S' hS' with ⟨_, hK', hcard'⟩
      have hk_not : k ∉ (expand n pre k S').2 := fun h => by
        have := Finset.mem_range.mp (hK' h); omega
      change (expand n pre k S').1.card = S.card + (insert k (expand n pre k S').2).card at heq
      rw [Finset.card_insert_of_notMem hk_not] at heq
      have hcard_un := Finset.card_union_add_card_inter (S.erase (n + 2 + k)) g.inputs.toFinset
      have hcard_er : (S.erase (n + 2 + k)).card = S.card - 1 := Finset.card_erase_of_mem hmem
      have hcard_g : g.inputs.toFinset.card ≤ 2 :=
        le_trans (List.toFinset_card_le _) (hlen k (by omega))
      have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨n + 2 + k, hmem⟩
      change S'.card + ((S.erase (n + 2 + k)) ∩ g.inputs.toFinset).card = _ at hcard_un
      have hS'_eq : S'.card = S.card + 1 := by omega
      have heq' : (expand n pre k S').1.card = S'.card + (expand n pre k S').2.card := by omega
      have hdisj_g : Disjoint (S.erase (n + 2 + k)) g.inputs.toFinset := by
        rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]; omega
      have hg_card2 : g.inputs.toFinset.card = 2 := by omega
      rcases Finset.mem_union.mp hmem with hA | hB
      · have hnotB : n + 2 + k ∉ B := Finset.disjoint_left.mp hdisj hA
        rw [if_pos hA, if_neg hnotB]
        set A' := (A.erase (n + 2 + k)) ∪ g.inputs.toFinset
        have hS'_AB : S' = A' ∪ B := by
          ext w; simp only [S', S, A', Finset.mem_union, Finset.mem_erase]
          by_cases hw : w = n + 2 + k
          · subst hw; simp [hnotB]
          · tauto
        have hdisj' : Disjoint A' B := by
          rw [Finset.disjoint_left]; intro w hwA hwB
          rcases Finset.mem_union.mp hwA with h1 | h2
          · exact Finset.disjoint_left.mp hdisj (Finset.mem_erase.mp h1).2 hwB
          · have hne : w ≠ n + 2 + k := fun h => hnotB (h ▸ hwB)
            exact Finset.disjoint_left.mp hdisj_g
              (Finset.mem_erase.mpr ⟨hne, Finset.mem_union_right A hwB⟩) h2
        rw [hS'_AB] at hS' heq'
        rcases ih (by omega) A' B hS' hdisj' heq' with ⟨hd, hcA, hcB, hun⟩
        have hA'_card : A'.card = A.card + 1 := by
          have hdA : Disjoint (A.erase (n + 2 + k)) g.inputs.toFinset := by
            rw [Finset.disjoint_left]; intro w hw1 hw2
            exact Finset.disjoint_left.mp hdisj_g
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw1).1, Finset.mem_union_left B (Finset.mem_erase.mp hw1).2⟩) hw2
          rw [Finset.card_union_of_disjoint hdA, Finset.card_erase_of_mem hA, hg_card2]
          have := Finset.card_pos.mpr ⟨n + 2 + k, hA⟩; omega
        have hk_notA : k ∉ (expand n pre k A').2 := fun h => by
          have := Finset.mem_range.mp (expand_subset_range n pre k A' h); omega
        refine ⟨hd, ?_, hcB, ?_⟩
        · change (expand n pre k A').1.card = A.card + (insert k (expand n pre k A').2).card
          rw [Finset.card_insert_of_notMem hk_notA]; omega
        · rw [if_pos hmem]; change (expand n pre k S').1 = (expand n pre k A').1 ∪ (expand n pre k B).1
          rw [hS'_AB]; exact hun
      · have hnotA : n + 2 + k ∉ A := Finset.disjoint_right.mp hdisj hB
        rw [if_neg hnotA, if_pos hB]
        set B' := (B.erase (n + 2 + k)) ∪ g.inputs.toFinset
        have hS'_AB : S' = A ∪ B' := by
          ext w; simp only [S', S, B', Finset.mem_union, Finset.mem_erase]
          by_cases hw : w = n + 2 + k
          · subst hw; simp [hnotA]
          · tauto
        have hdisj' : Disjoint A B' := by
          rw [Finset.disjoint_left]; intro w hwA hwB
          rcases Finset.mem_union.mp hwB with h1 | h2
          · exact Finset.disjoint_left.mp hdisj hwA (Finset.mem_erase.mp h1).2
          · have hne : w ≠ n + 2 + k := fun h => hnotA (h ▸ hwA)
            exact Finset.disjoint_left.mp hdisj_g
              (Finset.mem_erase.mpr ⟨hne, Finset.mem_union_left B hwA⟩) h2
        rw [hS'_AB] at hS' heq'
        rcases ih (by omega) A B' hS' hdisj' heq' with ⟨hd, hcA, hcB, hun⟩
        have hB'_card : B'.card = B.card + 1 := by
          have hdB : Disjoint (B.erase (n + 2 + k)) g.inputs.toFinset := by
            rw [Finset.disjoint_left]; intro w hw1 hw2
            exact Finset.disjoint_left.mp hdisj_g
              (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw1).1, Finset.mem_union_right A (Finset.mem_erase.mp hw1).2⟩) hw2
          rw [Finset.card_union_of_disjoint hdB, Finset.card_erase_of_mem hB, hg_card2]
          have := Finset.card_pos.mpr ⟨n + 2 + k, hB⟩; omega
        have hk_notB : k ∉ (expand n pre k B').2 := fun h => by
          have := Finset.mem_range.mp (expand_subset_range n pre k B' h); omega
        refine ⟨hd, hcA, ?_, ?_⟩
        · change (expand n pre k B').1.card = B.card + (insert k (expand n pre k B').2).card
          rw [Finset.card_insert_of_notMem hk_notB]; omega
        · rw [if_pos hmem]; change (expand n pre k S').1 = (expand n pre k A).1 ∪ (expand n pre k B').1
          rw [hS'_AB]; exact hun
    · have hnotA : n + 2 + k ∉ A := fun h => hmem (Finset.mem_union_left B h)
      have hnotB : n + 2 + k ∉ B := fun h => hmem (Finset.mem_union_right A h)
      rw [if_neg hmem] at heq
      rw [if_neg hnotA, if_neg hnotB]
      have hAB' : ∀ w ∈ A ∪ B, w < n + 2 + k := by
        intro w hw; have := hS w hw; have : w ≠ n + 2 + k := fun h => hmem (h ▸ hw); omega
      rcases ih (by omega) A B hAB' hdisj heq with ⟨hd, hcA, hcB, hun⟩
      exact ⟨hd, hcA, hcB, by rw [if_neg hmem]; exact hun⟩

lemma expand_allTrue_val (n : ℕ) (pre : List Gate)
    (hfit : ∀ j < pre.length, (pre.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∨
      (pre.getD j ⟨GateOp.or, []⟩).op = GateOp.or)
    (hrb : ∀ j < pre.length, ∀ i ∈ (pre.getD j ⟨GateOp.or, []⟩).inputs, i < n + 2 + j) :
    ∀ (k : ℕ), k ≤ pre.length → ∀ S : Finset ℕ, (∀ w ∈ S, w < n + 2 + k) →
      (∀ w ∈ (expand n pre k S).1, w < n) →
      (∀ j ∈ (expand n pre k S).2, (pre.getD j ⟨GateOp.or, []⟩).inputs ≠ []) →
      ∀ w ∈ S, wireVal n (pre.take k) (fun _ => true) w = true := by
  intro k
  induction k with
  | zero =>
    intro _ S _ hLn _ w hw
    simp only [List.take_zero]
    have hwn : w < n := hLn w hw
    exact wireVal_input_lt (fun _ => true) ⟨w, hwn⟩
  | succ k ih =>
    intro hk S hS hLn hne
    have htake : pre.take (k + 1) = pre.take k ++ [pre.getD k ⟨GateOp.or, []⟩] :=
      take_succ_eq_getD pre (by omega)
    have hlen_take : (pre.take k).length = k := List.length_take_of_le (by omega)
    let gk := pre.getD k ⟨GateOp.or, []⟩
    dsimp only [expand] at hLn hne
    by_cases hmem : n + 2 + k ∈ S
    · rw [if_pos hmem] at hLn hne
      let S' := (S.erase (n + 2 + k)) ∪ gk.inputs.toFinset
      have hS' : ∀ w ∈ S', w < n + 2 + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with h1 | h2
        · have := (Finset.mem_erase.mp h1).1; have := hS w (Finset.mem_erase.mp h1).2; omega
        · exact hrb k (by omega) w (List.mem_toFinset.mp h2)
      have hih := ih (by omega) S' hS' hLn (fun j hj => hne j (Finset.mem_insert_of_mem hj))
      intro w hw
      rw [htake]
      by_cases hwk : w = n + 2 + k
      · subst hwk
        have hwp := wireVal_push_new (n := n) (pre.take k) gk (fun _ => true)
        rw [hlen_take] at hwp
        rw [hwp]
        have hkne : gk.inputs ≠ [] := hne k (Finset.mem_insert_self ..)
        rcases hfit k (by omega) with hop | hop
        · rw [hop]; simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
          rintro _ ⟨i, hi, rfl⟩
          exact hih i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
        · rw [hop]; simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          cases hin : gk.inputs with
          | nil => exact absurd hin hkne
          | cons a as =>
            exact ⟨true, ⟨a, by simp, hih a (Finset.mem_union_right _ (List.mem_toFinset.mpr (by rw [hin]; simp)))⟩, rfl⟩
      · have hext : Extends n (pre.take k) (pre.take k ++ [gk]) := extends_push _ _
        have hw_lt : w < n + 2 + k := by have := hS w hw; omega
        rw [hext.2 _ w (by omega)]
        exact hih w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hw⟩))
    · rw [if_neg hmem] at hLn hne
      have hS' : ∀ w ∈ S, w < n + 2 + k := by
        intro w hw; have := hS w hw; have : w ≠ n + 2 + k := fun h => hmem (h ▸ hw); omega
      have hih := ih (by omega) S hS' hLn hne
      intro w hw
      rw [htake]
      have hext : Extends n (pre.take k) (pre.take k ++ [gk]) := extends_push _ _
      rw [hext.2 _ w (by have := hS' w hw; omega)]
      exact hih w hw

lemma expand_eq_tree_props (n : ℕ) (pre : List Gate)
    (hfit : ∀ j < pre.length, (pre.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∨
      (pre.getD j ⟨GateOp.or, []⟩).op = GateOp.or)
    (hlen : ∀ j < pre.length, (pre.getD j ⟨GateOp.or, []⟩).inputs.length ≤ 2)
    (hrb : ∀ j < pre.length, ∀ i ∈ (pre.getD j ⟨GateOp.or, []⟩).inputs, i < n + 2 + j) :
    ∀ (k : ℕ), k ≤ pre.length → ∀ S : Finset ℕ, (∀ w ∈ S, w < n + 2 + k) →
      (expand n pre k S).1.card = S.card + (expand n pre k S).2.card →
      (∀ w ∈ (expand n pre k S).1, w < n) →
      (∀ j ∈ (expand n pre k S).2, (pre.getD j ⟨GateOp.or, []⟩).inputs.length = 2) ∧
      ((∃ j ∈ (expand n pre k S).2, (pre.getD j ⟨GateOp.or, []⟩).op = GateOp.or) →
        ∃ u : Fin n, u.val ∈ (expand n pre k S).1 ∧
          ∀ w ∈ S, wireVal n (pre.take k) (fun t => decide (t ≠ u)) w = true) := by
  intro k
  induction k with
  | zero =>
    intro _ S _ _ _
    dsimp only [expand]
    exact ⟨fun _ h => absurd h (Finset.notMem_empty _), fun ⟨_, h, _⟩ => absurd h (Finset.notMem_empty _)⟩
  | succ k ih =>
    intro hk S hS heq hLn
    have htake : pre.take (k + 1) = pre.take k ++ [pre.getD k ⟨GateOp.or, []⟩] :=
      take_succ_eq_getD pre (by omega)
    have hlen_take : (pre.take k).length = k := List.length_take_of_le (by omega)
    set gk := pre.getD k ⟨GateOp.or, []⟩
    dsimp only [expand] at heq hLn ⊢
    by_cases hmem : n + 2 + k ∈ S
    · rw [if_pos hmem] at heq hLn ⊢
      set S' := (S.erase (n + 2 + k)) ∪ gk.inputs.toFinset
      have hS' : ∀ w ∈ S', w < n + 2 + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with h1 | h2
        · have := (Finset.mem_erase.mp h1).1; have := hS w (Finset.mem_erase.mp h1).2; omega
        · exact hrb k (by omega) w (List.mem_toFinset.mp h2)
      rcases expand_basic n pre hlen hrb k (by omega) S' hS' with ⟨_, hK', hcard'⟩
      have hk_not : k ∉ (expand n pre k S').2 := fun h => by
        have := Finset.mem_range.mp (hK' h); omega
      change (expand n pre k S').1.card = S.card + (insert k (expand n pre k S').2).card at heq
      rw [Finset.card_insert_of_notMem hk_not] at heq
      have hcard_un := Finset.card_union_add_card_inter (S.erase (n + 2 + k)) gk.inputs.toFinset
      change S'.card + ((S.erase (n + 2 + k)) ∩ gk.inputs.toFinset).card = _ at hcard_un
      have hcard_er : (S.erase (n + 2 + k)).card = S.card - 1 := Finset.card_erase_of_mem hmem
      have hcard_g : gk.inputs.toFinset.card ≤ gk.inputs.length := List.toFinset_card_le _
      have hglen2 : gk.inputs.length ≤ 2 := hlen k (by omega)
      have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨n + 2 + k, hmem⟩
      have hS'_eq : S'.card = S.card + 1 := by omega
      have heq' : (expand n pre k S').1.card = S'.card + (expand n pre k S').2.card := by omega
      have hgk_len2 : gk.inputs.length = 2 := by omega
      have hgk_card2 : gk.inputs.toFinset.card = 2 := by omega
      rcases ih (by omega) S' hS' heq' hLn with ⟨hlen_ih, hor_ih⟩
      refine ⟨?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hjk | hj'
        · rw [hjk]; exact hgk_len2
        · exact hlen_ih j hj'
      · rintro ⟨j, hj, hjor⟩
        rcases Finset.mem_insert.mp hj with hjk | hj'
        · rw [hjk] at hjor
          cases hin : gk.inputs with
          | nil => rw [hin] at hgk_len2; simp at hgk_len2
          | cons a tl =>
            cases tl with
            | nil => rw [hin] at hgk_len2; simp at hgk_len2
            | cons b tl2 =>
              cases tl2 with
              | cons _ _ => rw [hin] at hgk_len2; simp at hgk_len2
              | nil =>
                have hab : a ≠ b := by
                  intro h; rw [hin, h] at hgk_card2; simp at hgk_card2
                have haS' : a ∈ S' := Finset.mem_union_right _ (List.mem_toFinset.mpr (by rw [hin]; simp))
                have hbS' : b ∈ S' := Finset.mem_union_right _ (List.mem_toFinset.mpr (by rw [hin]; simp))
                let A : Finset ℕ := {a}
                let B : Finset ℕ := S'.erase a
                have hS'_AB : S' = A ∪ B := by
                  ext w; simp only [A, B, Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
                  by_cases h : w = a <;> simp [h, haS']
                have hdisj : Disjoint A B := by simp [A, B]
                rw [hS'_AB] at hS' heq'
                rcases expand_partition_eq n pre hlen hrb k (by omega) A B hS' hdisj heq' with
                  ⟨hdisjL, hcardA, _, hunL⟩
                have hAcard : A.card = 1 := Finset.card_singleton a
                have hLA_pos : 0 < (expand n pre k A).1.card := by omega
                rcases Finset.card_pos.mp hLA_pos with ⟨wu, hwuA⟩
                have hwuL : wu ∈ (expand n pre k S').1 := by
                  rw [hS'_AB, hunL]; exact Finset.mem_union_left _ hwuA
                have hwu_lt : wu < n := hLn wu hwuL
                let u : Fin n := ⟨wu, hwu_lt⟩
                have hu_notB : u.val ∉ (expand n pre k B).1 := Finset.disjoint_left.mp hdisjL hwuA
                have hB_agree : ∀ w ∈ B, wireVal n (pre.take k) (fun t => decide (t ≠ u)) w =
                    wireVal n (pre.take k) (fun _ => true) w := by
                  apply expand_agree n pre hrb _ _ k (by omega) B
                    (fun w hw => hS' w (Finset.mem_union_right A hw))
                  intro t ht
                  have htu : t ≠ u := fun h => hu_notB (h ▸ ht)
                  simp [htu]
                have hS'_true : ∀ w ∈ S', wireVal n (pre.take k) (fun _ => true) w = true := by
                  apply expand_allTrue_val n pre hfit hrb k (by omega) S' (hS'_AB ▸ hS') hLn
                  intro j' hj'; have := hlen_ih j' hj'; intro h; rw [h] at this; simp at this
                have hB_true : ∀ w ∈ B, wireVal n (pre.take k) (fun t => decide (t ≠ u)) w = true := by
                  intro w hw
                  rw [hB_agree w hw]
                  exact hS'_true w (Finset.mem_erase.mp hw).2
                refine ⟨u, hwuL, fun w hw => ?_⟩
                rw [htake]
                by_cases hwk : w = n + 2 + k
                · subst hwk
                  have hwp := wireVal_push_new (pre.take k) gk (fun t => decide (t ≠ u))
                  rw [hlen_take] at hwp
                  rw [hwp]
                  have hbB : b ∈ B := Finset.mem_erase.mpr ⟨hab.symm, hbS'⟩
                  have hbt := hB_true b hbB
                  have hgk_or : gk.op = GateOp.or := hjor
                  simp only [hgk_or, hin, GateOp.eval, List.map_cons, List.map_nil,
                    List.any_cons, List.any_nil, id_eq, Bool.or_false, hbt, Bool.or_true]
                · have hext : Extends n (pre.take k) (pre.take k ++ [gk]) := extends_push _ _
                  have hw_lt : w < n + 2 + k := by have := hS w hw; omega
                  rw [hext.2 _ w (by omega)]
                  have hdisj_g : Disjoint (S.erase (n + 2 + k)) gk.inputs.toFinset := by
                    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]; omega
                  have hwa : w ≠ a := fun h =>
                    Finset.disjoint_left.mp hdisj_g
                      (Finset.mem_erase.mpr ⟨hwk, hw⟩)
                      (h ▸ List.mem_toFinset.mpr (by rw [hin]; simp))
                  exact hB_true w (Finset.mem_erase.mpr ⟨hwa, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hw⟩)⟩)
        · -- j in K': use IH
          rcases hor_ih ⟨j, hj', hjor⟩ with ⟨u, huL, huTrue⟩
          refine ⟨u, huL, fun w hw => ?_⟩
          rw [htake]
          by_cases hwk : w = n + 2 + k
          · subst hwk
            have hwp := wireVal_push_new (pre.take k) gk (fun t => decide (t ≠ u))
            rw [hlen_take] at hwp
            rw [hwp]
            rcases hfit k (by omega) with hop | hop
            · rw [show gk.op = GateOp.and from hop]
              simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
              rintro _ ⟨i, hi, rfl⟩
              exact huTrue i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
            · rw [show gk.op = GateOp.or from hop]
              simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
              cases hin : gk.inputs with
              | nil => rw [hin] at hgk_len2; simp at hgk_len2
              | cons a as =>
                exact ⟨true, ⟨a, by simp, huTrue a (Finset.mem_union_right _ (List.mem_toFinset.mpr (by rw [hin]; simp)))⟩, rfl⟩
          · have hext : Extends n (pre.take k) (pre.take k ++ [gk]) := extends_push _ _
            have hw_lt : w < n + 2 + k := by have := hS w hw; omega
            rw [hext.2 _ w (by omega)]
            exact huTrue w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hw⟩))
    · rw [if_neg hmem] at heq hLn ⊢
      have hS' : ∀ w ∈ S, w < n + 2 + k := by
        intro w hw; have := hS w hw; have : w ≠ n + 2 + k := fun h => hmem (h ▸ hw); omega
      rcases ih (by omega) S hS' heq hLn with ⟨hlen_ih, hor_ih⟩
      refine ⟨hlen_ih, fun hor => ?_⟩
      rcases hor_ih hor with ⟨u, huL, huTrue⟩
      refine ⟨u, huL, fun w hw => ?_⟩
      rw [htake]
      have hext : Extends n (pre.take k) (pre.take k ++ [gk]) := extends_push _ _
      rw [hext.2 _ w (by have := hS' w hw; omega)]
      exact huTrue w hw

lemma expand_and_tree_false (n : ℕ) (pre : List Gate)
    (hrb : ∀ j < pre.length, ∀ i ∈ (pre.getD j ⟨GateOp.or, []⟩).inputs, i < n + 2 + j) :
    ∀ (k : ℕ), k ≤ pre.length → ∀ (S : Finset ℕ), (∀ w ∈ S, w < n + 2 + k) →
      (∀ w ∈ (expand n pre k S).1, w < n) →
      (∀ j ∈ (expand n pre k S).2, (pre.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∧
        (pre.getD j ⟨GateOp.or, []⟩).inputs ≠ []) →
      ∀ j ∈ (expand n pre k S).2, ∃ u : Fin n,
        wireVal n (pre.take k) (fun t => decide (t ≠ u)) (n + 2 + j) = false := by
  -- Stronger helper: for any S' whose expand has leaves < n and all gates AND/nonempty,
  -- every w in S' has some u making wireVal = false
  have hstrong : ∀ (k : ℕ), k ≤ pre.length → ∀ (S : Finset ℕ), (∀ w ∈ S, w < n + 2 + k) →
      (∀ w ∈ (expand n pre k S).1, w < n) →
      (∀ j ∈ (expand n pre k S).2, (pre.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∧
        (pre.getD j ⟨GateOp.or, []⟩).inputs ≠ []) →
      (∀ w ∈ S, ∃ u : Fin n, wireVal n (pre.take k) (fun t => decide (t ≠ u)) w = false) ∧
      (∀ j ∈ (expand n pre k S).2, ∃ u : Fin n,
        wireVal n (pre.take k) (fun t => decide (t ≠ u)) (n + 2 + j) = false) := by
    intro k
    induction k with
    | zero =>
      intro _ S _ hLn _
      dsimp only [expand] at hLn ⊢
      refine ⟨fun w hw => ?_, fun _ h => absurd h (Finset.notMem_empty _)⟩
      have hwn : w < n := hLn w hw
      refine ⟨⟨w, hwn⟩, ?_⟩
      simp only [List.take_zero]
      change wireVal n [] (fun t => decide (t ≠ ⟨w, hwn⟩)) (⟨w, hwn⟩ : Fin n).val = false
      rw [wireVal_input_lt]; simp
    | succ k ih =>
      intro hk S hS hLn hand
      have htake : pre.take (k + 1) = pre.take k ++ [pre.getD k ⟨GateOp.or, []⟩] :=
        take_succ_eq_getD pre (by omega)
      have hlen_take : (pre.take k).length = k := List.length_take_of_le (by omega)
      let gk := pre.getD k ⟨GateOp.or, []⟩
      have hext : Extends n (pre.take k) (pre.take k ++ [gk]) := extends_push _ _
      dsimp only [expand] at hLn hand ⊢
      by_cases hmem : n + 2 + k ∈ S
      · rw [if_pos hmem] at hLn hand ⊢
        let S' := (S.erase (n + 2 + k)) ∪ gk.inputs.toFinset
        have hS' : ∀ w ∈ S', w < n + 2 + k := by
          intro w hw
          rcases Finset.mem_union.mp hw with h1 | h2
          · have := (Finset.mem_erase.mp h1).1; have := hS w (Finset.mem_erase.mp h1).2; omega
          · exact hrb k (by omega) w (List.mem_toFinset.mp h2)
        rcases ih (by omega) S' hS' hLn (fun j hj => hand j (Finset.mem_insert_of_mem hj)) with ⟨ihS, ihK⟩
        rcases hand k (Finset.mem_insert_self ..) with ⟨hk_and, hk_ne⟩
        have hk_false : ∃ u : Fin n, wireVal n (pre.take (k + 1)) (fun t => decide (t ≠ u)) (n + 2 + k) = false := by
          cases hin : gk.inputs with
          | nil => exact absurd hin hk_ne
          | cons a as =>
            rcases ihS a (Finset.mem_union_right _ (List.mem_toFinset.mpr (by rw [hin]; simp))) with ⟨u, hu⟩
            refine ⟨u, ?_⟩
            rw [htake]
            have hwp := wireVal_push_new (pre.take k) gk (fun t => decide (t ≠ u))
            rw [hlen_take] at hwp
            rw [hwp]
            simp only [gk, hk_and, hin, GateOp.eval, List.map_cons, List.all_cons, id_eq, hu, Bool.false_and]
        refine ⟨fun w hw => ?_, fun j hj => ?_⟩
        · by_cases hwk : w = n + 2 + k
          · exact hwk ▸ hk_false
          · rcases ihS w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hw⟩)) with ⟨u, hu⟩
            refine ⟨u, ?_⟩
            rw [htake, hext.2 _ w (by have := hS w hw; omega), hu]
        · rcases Finset.mem_insert.mp hj with hjk | hj'
          · exact hjk ▸ hk_false
          · rcases ihK j hj' with ⟨u, hu⟩
            have hj_lt : j < k := Finset.mem_range.mp (expand_subset_range n pre k S' hj')
            refine ⟨u, ?_⟩
            rw [htake, hext.2 _ (n + 2 + j) (by omega), hu]
      · rw [if_neg hmem] at hLn hand ⊢
        have hS' : ∀ w ∈ S, w < n + 2 + k := by
          intro w hw; have := hS w hw; have : w ≠ n + 2 + k := fun h => hmem (h ▸ hw); omega
        rcases ih (by omega) S hS' hLn hand with ⟨ihS, ihK⟩
        refine ⟨fun w hw => ?_, fun j hj => ?_⟩
        · rcases ihS w hw with ⟨u, hu⟩
          refine ⟨u, ?_⟩; rw [htake, hext.2 _ w (by have := hS' w hw; omega), hu]
        · rcases ihK j hj with ⟨u, hu⟩
          have hj_lt : j < k := Finset.mem_range.mp (expand_subset_range n pre k S hj)
          refine ⟨u, ?_⟩; rw [htake, hext.2 _ (n + 2 + j) (by omega), hu]
  intro k hk S hS hLn hand
  exact (hstrong k hk S hS hLn hand).2

lemma base_lower_bound {n : ℕ} (G H : Finset (Fin n × Fin n))
    (hltG : ∀ e ∈ G, e.1 < e.2) (hHG : H ⊆ G) (hHne : H.Nonempty)
    (hact3 : 3 ≤ (H.image Prod.fst ∪ H.image Prod.snd).card)
    (C : Circuit) (tap : ↥H → Fin (n + 2 + C.size))
    (hfit : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (hout_lt : C.output < n + 2 + C.size)
    (hnc1 : PEqualNP.NotBracket.notCount C = 1)
    (hspec : ∀ x : Fin n → Bool,
      let wires := List.ofFn x ++ [false, true]
      (C.eval wires = true ↔ ∀ e ∈ G, x e.1 = true ∨ x e.2 = true) ∧
      ((∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
        ∀ e, (C.wires wires).getD (tap e).val false = xor (x e.val.1) (x e.val.2))) :
    (H.image Prod.fst ∪ H.image Prod.snd).card + H.card + 1 ≤ C.size := by
  let active := H.image Prod.fst ∪ H.image Prod.snd
  have hncL : notCountL C.gates = 1 := (notCountL_eq_notCount C).trans hnc1
  rcases split_unique_not C.gates hncL with ⟨pre, post, g0, hgs_eq, hg0_op, hpre0, hpost0⟩
  let j0 := pre.length
  have hfit_pre : ∀ g ∈ pre, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
    fun g hg => (hfit g (by rw [hgs_eq]; simp [hg])).1
  have hfit_post : ∀ g ∈ post, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
    fun g hg => (hfit g (by rw [hgs_eq]; simp [hg])).1
  -- Show g0.inputs is nonempty (otherwise NOT gate is constant true, contradicting drops)
  have hex_w0 : ∃ w0 : ℕ, g0.inputs.head? = some w0 := by
    cases hin : g0.inputs with
    | nil =>
      exfalso
      rcases hHne with ⟨e0, he0H⟩
      let x1 : Fin n → Bool := fun t => decide (t ≠ e0.1)
      let xT : Fin n → Bool := fun _ => true
      have hcov1 := cover_allExcept_singleton G hltG e0.1
      have hcovT : ∀ e ∈ G, xT e.1 = true ∨ xT e.2 = true := fun _ _ => Or.inl rfl
      have hmono : ∀ i, (C.wires (List.ofFn x1 ++ [false, true])).getD i false ≤
          (C.wires (List.ofFn xT ++ [false, true])).getD i false := by
        intro i
        change (evalWires C.gates _).getD i false ≤ (evalWires C.gates _).getD i false
        rw [hgs_eq, evalWires_append, evalWires_append, evalWires_append, evalWires_append]
        apply evalWires_mono_of_zero_not post hfit_post hpost0 _ _ (by simp [evalWires_length])
        have hpm := evalWires_mono_of_zero_not pre hfit_pre hpre0
          (List.ofFn x1 ++ [false, true]) (List.ofFn xT ++ [false, true]) (by simp)
          (inputs_le_of_pointwise (x := x1) (y := xT) (fun _ _ => rfl))
        exact getD_append_le (by simp [evalWires_length]) hpm (by simp [hg0_op, hin, GateOp.eval])
      have h1 := hmono (tap ⟨e0, he0H⟩).val
      have hne_e0 : e0.1 ≠ e0.2 := ne_of_lt (hltG e0 (hHG he0H))
      rw [(hspec x1).2 hcov1 ⟨e0, he0H⟩, (hspec xT).2 hcovT ⟨e0, he0H⟩] at h1
      simp [x1, xT, hne_e0.symm] at h1
      exact absurd h1 (by decide)
    | cons w0 _ => exact ⟨w0, rfl⟩
  rcases hex_w0 with ⟨w0, hw0_head⟩
  let g : (Fin n → Bool) → Bool := fun x => (C.wires (List.ofFn x ++ [false, true])).getD w0 false
  rcases one_not_guard_step C hfit hrb hnc1 pre post g0 hgs_eq hg0_op hpre0 hpost0 w0 hw0_head with
    ⟨hg_mono, hnot_val, _⟩
  have hj0_lt : j0 < C.gates.length := by rw [hgs_eq]; simp [j0]
  have hget_j0 : C.gates.get ⟨j0, hj0_lt⟩ = g0 := by
    simp only [List.get_eq_getElem]
    have h1 : C.gates[j0] = (pre ++ [g0] ++ post)[pre.length]'(by simp) := by
      simp only [hgs_eq, j0]
    rw [h1, getElem_append_mid]
  rcases conjunct1_fwd G H hltG hHG C tap hfit hrb hnc1 hspec g hg_mono ⟨j0, hj0_lt⟩ w0
    (hget_j0 ▸ hg0_op) (hget_j0 ▸ hw0_head) (fun _ => rfl) with ⟨_, hg_upper, hg_lower⟩
  have hg_allT : g (fun _ => true) = true := by
    rcases hHne with ⟨e0, he0H⟩
    have he1 : e0.1 ∈ active := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e0, he0H, rfl⟩)
    exact hg_lower (fun _ => true) (fun _ _ => Or.inl rfl) (fun _ _ => rfl) ⟨e0.1, he1, fun _ _ => rfl⟩
  have hg_single : ∀ u ∈ active, g (fun t => decide (t ≠ u)) = false := by
    intro u hu
    cases h : g (fun t => decide (t ≠ u))
    · rfl
    · have ht := hg_upper _ h u hu; simp at ht
  -- 1. All H.card taps are distinct and strictly above n + 2 + j0
  have htap_gt : ∀ e : ↥H, n + 2 + j0 < (tap e).val := by
    intro e
    by_contra hle
    by_cases heq : (tap e).val = n + 2 + j0
    · -- Pick u in active \ {e.1, e.2} using 3 <= active.card
      have hex_u : ∃ u ∈ active, u ≠ e.val.1 ∧ u ≠ e.val.2 := by
        have hsub : (active \ {e.val.1, e.val.2}).Nonempty := by
          apply Finset.card_pos.mp
          have h1 : ({e.val.1, e.val.2} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
          have h2 := Finset.card_sdiff_add_card_inter active {e.val.1, e.val.2}
          have h3 : (active ∩ {e.val.1, e.val.2}).card ≤ 2 :=
            le_trans (Finset.card_le_card Finset.inter_subset_right) h1
          have h4 : 3 ≤ active.card := hact3
          omega
        rcases hsub with ⟨u, hu⟩
        rcases Finset.mem_sdiff.mp hu with ⟨hu1, hu2⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu2
        exact ⟨u, hu1, hu2.1, hu2.2⟩
      rcases hex_u with ⟨u, hu_act, hu1, hu2⟩
      let xu : Fin n → Bool := fun t => decide (t ≠ u)
      have h1 := (hspec xu).2 (cover_allExcept_singleton G hltG u) e
      rw [heq, hnot_val xu] at h1
      change (!(g xu)) = xor (xu e.val.1) (xu e.val.2) at h1
      rw [hg_single u hu_act] at h1
      simp [xu, hu1.symm, hu2.symm] at h1
    · have hlt : (tap e).val < n + 2 + j0 := by omega
      let x1 : Fin n → Bool := fun t => decide (t ≠ e.val.1)
      let xT : Fin n → Bool := fun _ => true
      have hpre1 : (C.wires (List.ofFn x1 ++ [false, true])).getD (tap e).val false =
          (evalWires pre (List.ofFn x1 ++ [false, true])).getD (tap e).val false := by
        change (evalWires C.gates _).getD _ false = _
        rw [hgs_eq, List.append_assoc, evalWires_getD_prefix pre ([g0] ++ post) _ _ (by simp; omega)]
      have hpreT : (C.wires (List.ofFn xT ++ [false, true])).getD (tap e).val false =
          (evalWires pre (List.ofFn xT ++ [false, true])).getD (tap e).val false := by
        change (evalWires C.gates _).getD _ false = _
        rw [hgs_eq, List.append_assoc, evalWires_getD_prefix pre ([g0] ++ post) _ _ (by simp; omega)]
      have hm := evalWires_mono_of_zero_not pre hfit_pre hpre0
        (List.ofFn x1 ++ [false, true]) (List.ofFn xT ++ [false, true]) (by simp)
        (inputs_le_of_pointwise (x := x1) (y := xT) (fun _ _ => rfl)) (tap e).val
      rw [← hpre1, ← hpreT, (hspec x1).2 (cover_allExcept_singleton G hltG e.val.1) e,
          (hspec xT).2 (fun _ _ => Or.inl rfl) e] at hm
      have hne_e : e.val.1 ≠ e.val.2 := ne_of_lt (hltG e.val (hHG e.property))
      simp [x1, xT, hne_e.symm] at hm
      exact absurd hm (by decide)
  have htap_inj : Function.Injective (fun e : ↥H => (tap e).val) := by
    intro e1 e2 heq
    by_contra hne
    have hval_ne : e1.val ≠ e2.val := fun h => hne (Subtype.ext h)
    have hlt1 := hltG e1.val (hHG e1.property)
    have hlt2 := hltG e2.val (hHG e2.property)
    -- Two distinct ordered pairs with a < b cannot have the same underlying 2-element set
    have hex_diff : ∃ u : Fin n, (u = e1.val.1 ∨ u = e1.val.2) ↔ ¬ (u = e2.val.1 ∨ u = e2.val.2) := by
      by_cases h1 : e1.val.1 = e2.val.1 ∨ e1.val.1 = e2.val.2
      · by_cases h2 : e1.val.2 = e2.val.1 ∨ e1.val.2 = e2.val.2
        · exfalso
          rcases h1 with h1a | h1b <;> rcases h2 with h2a | h2b
          · rw [h1a, ← h2a] at hlt1; exact lt_irrefl _ hlt1
          · exact hval_ne (Prod.ext h1a h2b)
          · rw [h1b, h2a] at hlt1; exact lt_asymm hlt1 hlt2
          · rw [h1b, ← h2b] at hlt1; exact lt_irrefl _ hlt1
        · exact ⟨e1.val.2, by simp [h2]⟩
      · exact ⟨e1.val.1, by simp [h1]⟩
    rcases hex_diff with ⟨u, hu_iff⟩
    let xu : Fin n → Bool := fun t => decide (t ≠ u)
    have ht1 := (hspec xu).2 (cover_allExcept_singleton G hltG u) e1
    have ht2 := (hspec xu).2 (cover_allExcept_singleton G hltG u) e2
    dsimp only at heq
    rw [heq] at ht1
    have hxor_eq : xor (xu e1.val.1) (xu e1.val.2) = xor (xu e2.val.1) (xu e2.val.2) :=
      ht1.symm.trans ht2
    have hne1 : e1.val.1 ≠ e1.val.2 := ne_of_lt hlt1
    have hne2 : e2.val.1 ≠ e2.val.2 := ne_of_lt hlt2
    by_cases h1 : u = e1.val.1 ∨ u = e1.val.2
    · have h2 : ¬ (u = e2.val.1 ∨ u = e2.val.2) := hu_iff.mp h1
      push Not at h2
      have hx2 : xor (xu e2.val.1) (xu e2.val.2) = false := by
        simp [xu, h2.1.symm, h2.2.symm]
      have hx1 : xor (xu e1.val.1) (xu e1.val.2) = true := by
        rcases h1 with rfl | rfl <;> simp [xu, hne1, hne1.symm]
      rw [hx1, hx2] at hxor_eq; exact Bool.false_ne_true hxor_eq.symm
    · have h2 : u = e2.val.1 ∨ u = e2.val.2 := by
        by_contra hn; exact h1 (hu_iff.mpr hn)
      push Not at h1
      have hx1 : xor (xu e1.val.1) (xu e1.val.2) = false := by
        simp [xu, h1.1.symm, h1.2.symm]
      have hx2 : xor (xu e2.val.1) (xu e2.val.2) = true := by
        rcases h2 with rfl | rfl <;> simp [xu, hne2, hne2.symm]
      rw [hx1, hx2] at hxor_eq; exact Bool.false_ne_true hxor_eq
  let tapSet : Finset ℕ := (Finset.univ : Finset ↥H).image (fun e => (tap e).val)
  have htap_card : tapSet.card = H.card := by
    rw [Finset.card_image_of_injective _ htap_inj, Finset.card_univ, Fintype.card_coe]
  let postSet : Finset ℕ := Finset.Ioo (n + 2 + j0) (n + 2 + C.size)
  have hpost_card : postSet.card = post.length := by
    have hC_len : C.size = j0 + 1 + post.length := by
      change C.gates.length = pre.length + 1 + post.length; rw [hgs_eq]; simp; omega
    simp [postSet, Nat.card_Ioo]; omega
  have htap_sub : tapSet ⊆ postSet := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨e, _, rfl⟩
    exact Finset.mem_Ioo.mpr ⟨htap_gt e, (tap e).isLt⟩
  have hpost_ge : H.card ≤ post.length := by
    have := Finset.card_le_card htap_sub; omega
  -- 2. Cone expansion of w0 in pre
  have hw0_lt : w0 < n + 2 + j0 := by
    have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C j0 = g0 := by
      dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
      rw [hgs_eq, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [j0]),
          List.getElem?_append_right (by simp [j0])]; simp [j0]
    exact hrb j0 hj0_lt w0 (hgat ▸ List.mem_of_head? hw0_head)
  have hpre_fit_ao : ∀ j < pre.length, (pre.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∨
      (pre.getD j ⟨GateOp.or, []⟩).op = GateOp.or := by
    intro j hj
    have hgmem : pre.getD j ⟨GateOp.or, []⟩ ∈ pre := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
    have h1 := hfit_pre _ hgmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hpos : 0 < (pre.filter fun g => isNotOp g.op).length :=
        List.length_pos_of_mem (List.mem_filter.mpr ⟨hgmem, by rw [h]; rfl⟩)
      dsimp only [notCountL] at hpre0; omega
  have hpre_len2 : ∀ j < pre.length, (pre.getD j ⟨GateOp.or, []⟩).inputs.length ≤ 2 := by
    intro j hj
    have hgmem : pre.getD j ⟨GateOp.or, []⟩ ∈ pre := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
    exact (hfit _ (by rw [hgs_eq]; exact List.mem_append_left _ (List.mem_append_left _ hgmem))).2
  have hpre_rb : ∀ j < pre.length, ∀ i ∈ (pre.getD j ⟨GateOp.or, []⟩).inputs, i < n + 2 + j := by
    intro j hj i hi
    have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C j = pre.getD j ⟨GateOp.or, []⟩ := by
      dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
      rw [hgs_eq, List.append_assoc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hj]
    exact hrb j (lt_trans hj hj0_lt) i (hgat ▸ hi)
  set res := expand n pre j0 {w0}
  rcases expand_basic n pre hpre_len2 hpre_rb j0 le_rfl {w0} (by simp [hw0_lt]) with ⟨hL_lt, hK_sub, hL_card⟩
  have hact_sub_L : active.image Fin.val ⊆ res.1 := by
    intro wu hwu
    rcases Finset.mem_image.mp hwu with ⟨u, hu_act, rfl⟩
    by_contra hnot
    have hag := expand_agree n pre hpre_rb (fun t => decide (t ≠ u)) (fun _ => true)
      j0 le_rfl {w0} (by simp [hw0_lt]) (fun t ht => by
        have htu : t ≠ u := fun h => hnot (h ▸ ht); simp [htu]) w0 (Finset.mem_singleton_self _)
    rw [List.take_length] at hag
    have hgw : ∀ x : Fin n → Bool, g x = wireVal n pre x w0 := by
      intro x
      dsimp only [g, wireVal]
      change (evalWires C.gates _).getD w0 false = _
      rw [hgs_eq, List.append_assoc, evalWires_getD_prefix pre ([g0] ++ post) _ w0 (by simp; omega)]
    rw [← hgw, ← hgw, hg_single u hu_act, hg_allT] at hag
    exact Bool.false_ne_true hag
  have hact_le_L : active.card ≤ res.1.card := by
    have hinj : Function.Injective (Fin.val : Fin n → ℕ) := Fin.val_injective
    rw [← Finset.card_image_of_injective active hinj]
    exact Finset.card_le_card hact_sub_L
  have hK_le_j0 : res.2.card ≤ j0 := by
    have := Finset.card_le_card hK_sub; simpa using this
  have hL_card' : res.1.card ≤ 1 + res.2.card := by
    simpa [res] using hL_card
  have hC_eq : C.size = j0 + 1 + post.length := by
    change C.gates.length = pre.length + 1 + post.length; rw [hgs_eq]; simp; omega
  -- 3. Analyze C.output to gain the +1 gate!
  have hout_ge_in : n + 2 ≤ C.output := by
    by_contra hlt
    have : C.output < n ∨ C.output = n ∨ C.output = n + 1 := by omega
    rcases this with hn | hcn | hcn1
    · let u : Fin n := ⟨C.output, hn⟩
      let xu : Fin n → Bool := fun t => decide (t ≠ u)
      have hev := (hspec xu).1.mpr (cover_allExcept_singleton G hltG u)
      dsimp only [Circuit.eval] at hev
      change (evalWires ([] ++ C.gates) _).getD u.val false = true at hev
      rw [evalWires_getD_prefix [] C.gates _ u.val (by simp; omega)] at hev
      have hv := wireVal_input_lt xu u
      change (evalWires [] _).getD u.val false = xu u at hv
      rw [hv] at hev; simp [xu] at hev
    · have hev := (hspec (fun _ => true)).1.mpr (fun _ _ => Or.inl rfl)
      dsimp only [Circuit.eval] at hev
      rw [hcn] at hev
      change (evalWires ([] ++ C.gates) _).getD n false = true at hev
      rw [evalWires_getD_prefix [] C.gates _ n (by simp)] at hev
      have hv := wireVal_const_false (fun _ : Fin n => true)
      change (evalWires [] _).getD n false = false at hv
      rw [hv] at hev; exact Bool.false_ne_true hev
    · rcases hHne with ⟨e0, he0H⟩
      let x0 : Fin n → Bool := fun t => decide (t ≠ e0.1 ∧ t ≠ e0.2)
      have hncov : ¬ ∀ e ∈ G, x0 e.1 = true ∨ x0 e.2 = true := by
        intro hc; rcases hc e0 (hHG he0H) with h | h <;> simp [x0] at h
      have hev : C.eval (List.ofFn x0 ++ [false, true]) = true := by
        dsimp only [Circuit.eval]
        rw [hcn1]
        change (evalWires ([] ++ C.gates) _).getD (n + 1) false = true
        rw [evalWires_getD_prefix [] C.gates _ (n + 1) (by simp)]
        exact wireVal_const_true x0
      exact hncov ((hspec x0).1.mp hev)
  have hout_ne_j0 : C.output ≠ n + 2 + j0 := by
    intro heq
    have hev := (hspec (fun _ => true)).1.mpr (fun _ _ => Or.inl rfl)
    dsimp only [Circuit.eval] at hev
    rw [heq, hnot_val (fun _ => true)] at hev
    change (!(g (fun _ => true))) = true at hev
    rw [hg_allT] at hev
    exact Bool.false_ne_true hev
  have hout_not_tap : C.output ∉ tapSet := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨e, _, heq⟩
    have hev := (hspec (fun _ => true)).1.mpr (fun _ _ => Or.inl rfl)
    have hte := (hspec (fun _ => true)).2 (fun _ _ => Or.inl rfl) e
    dsimp only [Circuit.eval] at hev
    rw [← heq, hte] at hev; simp at hev
  by_cases hout_post : n + 2 + j0 < C.output
  · -- C.output is in postSet \ tapSet -> post.length >= H.card + 1
    have hsub' : insert C.output tapSet ⊆ postSet := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hmem
      · exact Finset.mem_Ioo.mpr ⟨hout_post, hout_lt⟩
      · exact htap_sub hmem
    have hcard_p := Finset.card_le_card hsub'
    rw [Finset.card_insert_of_notMem hout_not_tap, htap_card, hpost_card] at hcard_p
    simp only [Finset.card_singleton] at hL_card
    change active.card + H.card + 1 ≤ C.size
    omega
  · -- C.output < n + 2 + j0 -> j_out := C.output - (n + 2) < j0
    let jOut := C.output - (n + 2)
    have hjOut_lt : jOut < j0 := by omega
    by_cases hbig : active.card ≤ j0
    · change active.card + H.card + 1 ≤ C.size
      omega
    · -- Only remaining case: j0 = active.card - 1, res.2.card = j0, res.1 = active.image Fin.val, jOut in res.2
      simp only [Finset.card_singleton] at hL_card
      have hj0_eq : j0 = active.card - 1 := by omega
      have hK_eq : res.2.card = j0 := by omega
      have hL_eq_card : res.1.card = active.card := by omega
      have hK_all : res.2 = Finset.range j0 := Finset.eq_of_subset_of_card_le hK_sub (by simp [hK_eq])
      have hjOut_K : jOut ∈ res.2 := by rw [hK_all]; exact Finset.mem_range.mpr hjOut_lt
      have hL_eq : res.1 = active.image Fin.val :=
        (Finset.eq_of_subset_of_card_le hact_sub_L (by
          rw [Finset.card_image_of_injective _ Fin.val_injective]; omega)).symm
      have hLn : ∀ w ∈ res.1, w < n := by
        intro w hw; rw [hL_eq] at hw; rcases Finset.mem_image.mp hw with ⟨u, _, rfl⟩; exact u.isLt
      have heq_tree : res.1.card = ({w0} : Finset ℕ).card + res.2.card := by simp; omega
      rcases expand_eq_tree_props n pre hpre_fit_ao hpre_len2 hpre_rb j0 le_rfl {w0}
        (by simp [hw0_lt]) heq_tree hLn with ⟨hK_len2, hK_no_or⟩
      have hK_all_and : ∀ j ∈ res.2, (pre.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∧
          (pre.getD j ⟨GateOp.or, []⟩).inputs ≠ [] := by
        intro j hj
        have hjl : j < pre.length := Finset.mem_range.mp (hK_sub hj)
        refine ⟨?_, fun h => by have := hK_len2 j hj; rw [h] at this; simp at this⟩
        rcases hpre_fit_ao j hjl with hand | hor
        · exact hand
        · exfalso
          rcases hK_no_or ⟨j, hj, hor⟩ with ⟨u, huL, huTrue⟩
          have hu_act : u ∈ active := by
            rw [hL_eq] at huL
            rcases Finset.mem_image.mp huL with ⟨u', hu', heq⟩
            exact (Fin.ext heq) ▸ hu'
          have hwt := huTrue w0 (Finset.mem_singleton_self _)
          rw [List.take_length] at hwt
          have hgw : g (fun t => decide (t ≠ u)) = wireVal n pre (fun t => decide (t ≠ u)) w0 := by
            dsimp only [g, wireVal]
            change (evalWires C.gates _).getD w0 false = _
            rw [hgs_eq, List.append_assoc, evalWires_getD_prefix pre ([g0] ++ post) _ w0 (by simp; omega)]
          rw [← hgw, hg_single u hu_act] at hwt
          exact Bool.false_ne_true hwt
      rcases expand_and_tree_false n pre hpre_rb j0 le_rfl {w0} (by simp [hw0_lt]) hLn hK_all_and
        jOut hjOut_K with ⟨u, hu_false⟩
      rw [List.take_length] at hu_false
      have hev := (hspec (fun t => decide (t ≠ u))).1.mpr (cover_allExcept_singleton G hltG u)
      dsimp only [Circuit.eval] at hev
      have hpre_out : (C.wires (List.ofFn (fun t => decide (t ≠ u)) ++ [false, true])).getD C.output false =
          wireVal n pre (fun t => decide (t ≠ u)) (n + 2 + jOut) := by
        have hco : C.output = n + 2 + jOut := by dsimp only [jOut]; omega
        rw [hco]
        dsimp only [wireVal]
        change (evalWires C.gates _).getD (n + 2 + jOut) false = _
        rw [hgs_eq, List.append_assoc, evalWires_getD_prefix pre ([g0] ++ post) _ (n + 2 + jOut) (by simp; omega)]
      rw [hpre_out, hu_false] at hev
      exact False.elim (Bool.false_ne_true hev)

lemma conjunct2 {n : ℕ} :
    ∀ (d : ℕ) (G H : Finset (Fin n × Fin n)),
      (∀ e ∈ G, e.1 < e.2) → H ⊆ G → H.Nonempty →
      ∀ (drop : Fin d ↪ Fin n),
        (∀ j, drop j ∉ H.image Prod.fst ∪ H.image Prod.snd) →
        (∀ j : Fin d, ∃ v : Fin n, ((drop j, v) ∈ G ∨ (v, drop j) ∈ G) ∧
          ∀ h : Fin d, h.val < j.val → drop h ≠ v) →
        ∀ C : Circuit,
          (PEqualNP.MetaComplexity.FanInTwo C ∧
           PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
           C.output < n + 2 + C.size) →
          (∃ tap : ↥H → Fin (n + 2 + C.size), ∀ x : Fin n → Bool,
            let wires := List.ofFn x ++ [false, true]
            (C.eval wires = true ↔ ∀ e ∈ G, x e.1 = true ∨ x e.2 = true) ∧
            ((∀ e ∈ G, x e.1 = true ∨ x e.2 = true) →
              ∀ e, (C.wires wires).getD (tap e).val false = xor (x e.val.1) (x e.val.2))) →
          PEqualNP.NotBracket.notCount C = 1 →
          3 ≤ (H.image Prod.fst ∪ H.image Prod.snd).card →
          (H.image Prod.fst ∪ H.image Prod.snd).card + H.card + 1 + d ≤ C.size := by
  intro d
  induction d with
  | zero =>
    intro G H hltG hHG hHne _ _ _ C ⟨hfit, hrb, hout_lt⟩ ⟨tap, hspec⟩ hnc1 hact3
    have h := base_lower_bound G H hltG hHG hHne hact3 C tap hfit hrb hout_lt hnc1 hspec
    omega
  | succ d ih =>
    intro G H hltG hHG hHne drop hdrop_out hdrop_adj C ⟨hfit, hrb, hout_lt⟩ ⟨tap, hspec⟩ hnc1 hact3
    let u := drop 0
    rcases hdrop_adj 0 with ⟨v, huv, _⟩
    rcases eliminate_outside_site G H hltG hHG hHne u v (hdrop_out 0) huv C tap
      hfit hrb hout_lt hnc1 hspec with ⟨C', tap', hsize', hfit', hrb', hout', hnc', hspec'⟩
    let G' := G.filter (fun e => e.1 ≠ u ∧ e.2 ≠ u)
    have hltG' : ∀ e ∈ G', e.1 < e.2 := fun e he => hltG e (Finset.mem_filter.mp he).1
    have hHG' : H ⊆ G' := by
      intro e heH
      refine Finset.mem_filter.mpr ⟨hHG heH, ?_, ?_⟩
      · intro h1; exact hdrop_out 0 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, heH, h1⟩))
      · intro h2; exact hdrop_out 0 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, heH, h2⟩))
    let drop' : Fin d ↪ Fin n := ⟨fun j => drop j.succ, fun a b h => Fin.succ_injective _ (drop.injective h)⟩
    have hdrop'_out : ∀ j, drop' j ∉ H.image Prod.fst ∪ H.image Prod.snd := fun j => hdrop_out j.succ
    have hdrop'_adj : ∀ j : Fin d, ∃ w : Fin n, ((drop' j, w) ∈ G' ∨ (w, drop' j) ∈ G') ∧
        ∀ h : Fin d, h.val < j.val → drop' h ≠ w := by
      intro j
      rcases hdrop_adj j.succ with ⟨w, hw_adj, hw_prev⟩
      have hwu : w ≠ u := (hw_prev 0 (Nat.zero_lt_succ j.val)).symm
      have hju : drop' j ≠ u := fun h => by
        have := drop.injective h; exact Fin.succ_ne_zero j this
      refine ⟨w, ?_, fun h hh => hw_prev h.succ (Nat.succ_lt_succ hh)⟩
      rcases hw_adj with h1 | h2
      · exact Or.inl (Finset.mem_filter.mpr ⟨h1, hju, hwu⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨h2, hwu, hju⟩)
    have hrec := ih G' H hltG' hHG' hHne drop' hdrop'_out hdrop'_adj C'
      ⟨hfit', hrb', hout'⟩ ⟨tap', hspec'⟩ hnc' hact3
    omega

theorem main :
    ∀ (n : Nat) (G H : Finset (Fin n × Fin n)), (∀ e ∈ G, e.1 < e.2) → H ⊆ G →
      let V := Fin n
      let active := H.image Prod.fst ∪ H.image Prod.snd
      let adj := fun (u v : V) => (u,v) ∈ G ∨ (v,u) ∈ G
      let cover := fun (x : V → Bool) => ∀ e ∈ G, x e.1 = true ∨ x e.2 = true
      let shape := fun (m : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (m + 2) C ∧ C.output < m + 2 + C.size
      let marked := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        shape n C ∧ ∃ tap : ↥H → Fin (n + 2 + C.size), ∀ x : V → Bool,
          let wires := List.ofFn x ++ [false,true]
          (C.eval wires = true ↔ cover x) ∧
          (cover x → ∀ e, (C.wires wires).getD (tap e).val false = xor (x e.val.1) (x e.val.2))
      H.Nonempty →
        (∀ g : (V → Bool) → Bool, (∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true) →
          ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, marked C ∧ PEqualNP.NotBracket.notCount C = 1 ∧
            ∃ (j : Fin C.gates.length) (w : Nat),
              (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
              (C.gates.get j).inputs.head? = some w ∧
              ∀ x : V → Bool, (C.wires (List.ofFn x ++ [false,true])).getD w false = g x) ↔
           (∀ i ∈ active, ∀ j ∈ active, i ≠ j → adj i j) ∧
           (∀ x, g x = true → ∀ i ∈ active, x i = true) ∧
           (∀ x, cover x → (∀ i ∈ active, x i = true) →
             (∃ i ∈ active, ∀ j, adj i j → x j = true) → g x = true))) ∧
        (∀ (d : Nat) (drop : Fin d ↪ V), (∀ j, drop j ∉ active) →
          (∀ j : Fin d, ∃ v : V, adj (drop j) v ∧ ∀ h : Fin d, h.val < j.val → drop h ≠ v) →
          ∀ C : PEqualNP.CircuitLowerBounds.Circuit, marked C → PEqualNP.NotBracket.notCount C = 1 →
            3 ≤ active.card → active.card + H.card + 1 + d ≤ C.size) := by
  intro n G H hltG hHG
  dsimp only
  intro hHne
  constructor
  · intro g hg_mono
    constructor
    · rintro ⟨C, ⟨⟨hfit, hrb, _⟩, ⟨tap, hspec⟩⟩, hnc1, j, w, hj_op, hj_head, hg_eq⟩
      exact conjunct1_fwd G H hltG hHG C tap hfit hrb hnc1 hspec g hg_mono j w hj_op hj_head hg_eq
    · rintro ⟨hclique, hupper, hlower⟩
      rcases conjunct1_bwd G H hHG g hg_mono hclique hupper hlower with ⟨C, hsh, htap, hnc1, hnot⟩
      exact ⟨C, ⟨hsh, htap⟩, hnc1, hnot⟩
  · intro d drop hdrop_out hdrop_adj C ⟨hsh, htap⟩ hnc1 hact3
    exact conjunct2 d G H hltG hHG hHne drop hdrop_out hdrop_adj C hsh htap hnc1 hact3

end PEqualNP.Outside.L_lib_1187_aux

theorem PEqualNP.Outside.L_lib_1187 :
∀ (n : Nat) (G H : Finset (Fin n × Fin n)), (∀ e ∈ G, e.1 < e.2) → H ⊆ G →
  let V := Fin n
  let active := H.image Prod.fst ∪ H.image Prod.snd
  let adj := fun (u v : V) => (u,v) ∈ G ∨ (v,u) ∈ G
  let cover := fun (x : V → Bool) => ∀ e ∈ G, x e.1 = true ∨ x e.2 = true
  let shape := fun (m : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (m + 2) C ∧ C.output < m + 2 + C.size
  let marked := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    shape n C ∧ ∃ tap : ↥H → Fin (n + 2 + C.size), ∀ x : V → Bool,
      let wires := List.ofFn x ++ [false,true]
      (C.eval wires = true ↔ cover x) ∧
      (cover x → ∀ e, (C.wires wires).getD (tap e).val false = xor (x e.val.1) (x e.val.2))
  H.Nonempty →
    (∀ g : (V → Bool) → Bool, (∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true) →
      ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, marked C ∧ PEqualNP.NotBracket.notCount C = 1 ∧
        ∃ (j : Fin C.gates.length) (w : Nat),
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          (C.gates.get j).inputs.head? = some w ∧
          ∀ x : V → Bool, (C.wires (List.ofFn x ++ [false,true])).getD w false = g x) ↔
       (∀ i ∈ active, ∀ j ∈ active, i ≠ j → adj i j) ∧
       (∀ x, g x = true → ∀ i ∈ active, x i = true) ∧
       (∀ x, cover x → (∀ i ∈ active, x i = true) →
         (∃ i ∈ active, ∀ j, adj i j → x j = true) → g x = true))) ∧
    (∀ (d : Nat) (drop : Fin d ↪ V), (∀ j, drop j ∉ active) →
      (∀ j : Fin d, ∃ v : V, adj (drop j) v ∧ ∀ h : Fin d, h.val < j.val → drop h ≠ v) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, marked C → PEqualNP.NotBracket.notCount C = 1 →
        3 ≤ active.card → active.card + H.card + 1 + d ≤ C.size) :=
  PEqualNP.Outside.L_lib_1187_aux.main
