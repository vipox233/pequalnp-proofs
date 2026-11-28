import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1330

open PEqualNP.CircuitLowerBounds

private theorem andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
private theorem orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
private theorem notEval_nil : GateOp.not.eval [] = true := rfl
private theorem notEval_cons (a : Bool) (as : List Bool) : GateOp.not.eval (a :: as) = !a := rfl

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih, List.length_append, List.length_singleton, List.length_cons]
    omega

private theorem run_append (gs1 gs2 : List Gate) (x : List Bool) :
    run (gs1 ++ gs2) x = run gs2 (run gs1 x) := by
  simp [run, List.foldl_append]

private theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x =
      run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  rw [run_append]; simp [run]

private theorem getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_eq {α : Type} (l1 : List α) (a d : α) :
    (l1 ++ [a]).getD l1.length d = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp

private theorem run_prefix (gs1 gs2 : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs1.length) :
    (run (gs1 ++ gs2) x).getD i false = (run gs1 x).getD i false := by
  rw [run_append]
  have hgen : ∀ (gs : List Gate) (w : List Bool), i < w.length → (run gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w _; rfl
    | cons g gs ih =>
      intro w hw
      change (run gs (w ++ _)).getD i false = w.getD i false
      rw [ih (w ++ _) (by rw [List.length_append]; omega)]
      exact getD_append_left w _ i false hw
  exact hgen gs2 (run gs1 x) (by rw [run_length]; exact hi)

private theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  simpa [run] using run_prefix [] gs x i (by simpa using hi)

private theorem run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < x.length + j then (run gs x).getD i false else false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 : gs.take j ++ gs.drop j = gs := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1; simpa [List.append_assoc] using h1.symm
  have hlen : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hpref1 : (run gs x).getD (x.length + j) false =
      (run (gs.take j ++ [gs[j]]) x).getD (x.length + j) false := by
    conv_lhs => rw [hsplit]
    exact run_prefix (gs.take j ++ [gs[j]]) (gs.drop (j + 1)) x (x.length + j)
      (by rw [List.length_append, hlen, List.length_singleton]; omega)
  rw [hpref1, run_snoc]
  have hlen2 : (run (gs.take j) x).length = x.length + j := by rw [run_length, hlen]
  conv_lhs => rw [← hlen2]
  rw [getD_append_eq]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + j
  · simp only [if_pos hi]
    have htake : (run gs x).getD i false = (run (gs.take j) x).getD i false := by
      conv_lhs => rw [hsplit, List.append_assoc]
      exact run_prefix (gs.take j) ([gs[j]] ++ gs.drop (j + 1)) x i (by rw [hlen]; exact hi)
    exact htake.symm
  · simp only [if_neg hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

private theorem notCount_append (gs1 gs2 : List Gate) :
    PEqualNP.NotBracket.notCount ⟨gs1 ++ gs2, 0⟩ =
    PEqualNP.NotBracket.notCount ⟨gs1, 0⟩ + PEqualNP.NotBracket.notCount ⟨gs2, 0⟩ := by
  dsimp only [PEqualNP.NotBracket.notCount]
  rw [List.filter_append, List.length_append]

private theorem notCount_snoc (gs : List Gate) (g : Gate) :
    PEqualNP.NotBracket.notCount ⟨gs ++ [g], 0⟩ =
    PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + (match g.op with | .not => 1 | _ => 0) := by
  dsimp only [PEqualNP.NotBracket.notCount]
  rw [List.filter_append, List.length_append]
  cases h : g.op <;> simp [h]

private theorem notCount_le_len (gs : List Gate) :
    PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ gs.length :=
  List.length_filter_le _ _

-- Valid gate list on N+2 inputs
private def Ctx (N : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) ∧
  (∀ i < gs.length, ∀ w ∈ (gs.getD i ⟨.or, []⟩).inputs, w < N + 2 + i)

private theorem ctx_nil (N : ℕ) : Ctx N [] := ⟨by simp, by simp⟩

private theorem ctx_snoc (N : ℕ) (gs : List Gate) (g : Gate) (hctx : Ctx N gs)
    (hfan : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hrb : ∀ w ∈ g.inputs, w < N + 2 + gs.length) :
    Ctx N (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hctx.1 g' h1
    · rw [List.mem_singleton.mp h2]; exact hfan
  · intro i hi w hw
    rw [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < gs.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD] at hw
      exact hctx.2 i hlt w hw
    · have hieq : i = gs.length := by omega
      subst hieq
      have hge : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
      rw [hge] at hw
      exact hrb w hw

-- Raw input block indexing helpers
private theorem flatten_ofFn_length {α : Type} {k m : ℕ} (f : Fin k → List α)
    (hlen : ∀ i : Fin k, (f i).length = m) :
    (List.ofFn f).flatten.length = k * m := by
  rw [List.length_flatten, List.map_ofFn]
  have hconst : (List.length ∘ f) = fun _ => m := funext hlen
  rw [hconst, List.ofFn_const, List.sum_replicate, smul_eq_mul]

private theorem flatten_ofFn_getElem {α : Type} {k m : ℕ} (f : Fin k → List α)
    (hlen : ∀ i : Fin k, (f i).length = m) (i : Fin k) (r : ℕ) (hr : r < m) :
    ((List.ofFn f).flatten)[i.val * m + r]'(by
      rw [flatten_ofFn_length f hlen]
      have : (i.val + 1) * m ≤ k * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt i.isLt)
      rw [Nat.add_mul, Nat.one_mul] at this; omega) =
    (f i)[r]'(by rw [hlen i]; exact hr) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [List.ofFn_succ, List.flatten_cons, Fin.val_zero, Nat.zero_mul, Nat.zero_add]
      rw [List.getElem_append_left (by rw [hlen 0]; exact hr)]
    | succ i' =>
      simp only [List.ofFn_succ, List.flatten_cons, Fin.val_succ, Nat.add_mul, Nat.one_mul]
      have h1 : m ≤ i'.val * m + m + r := by omega
      rw [List.getElem_append_right (by rw [hlen 0]; exact h1)]
      have heq : i'.val * m + m + r - (f 0).length = i'.val * m + r := by rw [hlen 0]; omega
      simp only [heq]
      exact ih (fun j => f j.succ) (fun j => hlen j.succ) i'

private def rawClean (d k : ℕ) (s : Fin k) (x : Fin d → Bool) : List Bool :=
  (List.ofFn (fun i : Fin k => decide (i.val ≤ s.val) :: List.ofFn (fun z : Fin d =>
    decide (i.val < s.val) || (decide (i.val = s.val) && x z)))).flatten ++ [false, true]

private theorem rawClean_length (d k : ℕ) (s : Fin k) (x : Fin d → Bool) :
    (rawClean d k s x).length = k * (d + 1) + 2 := by
  dsimp only [rawClean]
  rw [List.length_append, flatten_ofFn_length (m := d + 1) _ (fun _ => by simp)]
  rfl

private theorem rawClean_marker (d k : ℕ) (s : Fin k) (x : Fin d → Bool) (i : Fin k) :
    (rawClean d k s x).getD (i.val * (d + 1)) false = decide (i.val ≤ s.val) := by
  dsimp only [rawClean]
  have hlen : (List.ofFn (fun i : Fin k => decide (i.val ≤ s.val) :: List.ofFn (fun z : Fin d =>
      decide (i.val < s.val) || (decide (i.val = s.val) && x z)))).flatten.length = k * (d + 1) :=
    flatten_ofFn_length _ (fun _ => by simp)
  have hlt : i.val * (d + 1) < k * (d + 1) := by
    have : (i.val + 1) * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt i.isLt)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  rw [getD_append_left _ _ _ _ (by rw [hlen]; exact hlt), List.getD_eq_getElem _ _ (by rw [hlen]; exact hlt)]
  have h := flatten_ofFn_getElem (k := k) (m := d + 1)
    (fun i : Fin k => decide (i.val ≤ s.val) :: List.ofFn (fun z : Fin d =>
      decide (i.val < s.val) || (decide (i.val = s.val) && x z)))
    (fun _ => by simp) i 0 (Nat.zero_lt_succ d)
  simpa using h

private theorem rawClean_data (d k : ℕ) (s : Fin k) (x : Fin d → Bool) (i : Fin k) (z : Fin d) :
    (rawClean d k s x).getD (i.val * (d + 1) + 1 + z.val) false =
      (decide (i.val < s.val) || (decide (i.val = s.val) && x z)) := by
  dsimp only [rawClean]
  have hlen : (List.ofFn (fun i : Fin k => decide (i.val ≤ s.val) :: List.ofFn (fun z : Fin d =>
      decide (i.val < s.val) || (decide (i.val = s.val) && x z)))).flatten.length = k * (d + 1) :=
    flatten_ofFn_length _ (fun _ => by simp)
  have hlt : i.val * (d + 1) + (1 + z.val) < k * (d + 1) := by
    have : (i.val + 1) * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt i.isLt)
    rw [Nat.add_mul, Nat.one_mul] at this; have := z.isLt; omega
  have heq_idx : i.val * (d + 1) + 1 + z.val = i.val * (d + 1) + (1 + z.val) := by omega
  rw [heq_idx, getD_append_left _ _ _ _ (by rw [hlen]; exact hlt), List.getD_eq_getElem _ _ (by rw [hlen]; exact hlt)]
  have h := flatten_ofFn_getElem (k := k) (m := d + 1)
    (fun i : Fin k => decide (i.val ≤ s.val) :: List.ofFn (fun z : Fin d =>
      decide (i.val < s.val) || (decide (i.val = s.val) && x z)))
    (fun _ => by simp) i (1 + z.val) (by have := z.isLt; omega)
  simpa [Nat.add_comm] using h

private theorem rawClean_false (d k : ℕ) (s : Fin k) (x : Fin d → Bool) :
    (rawClean d k s x).getD (k * (d + 1)) false = false := by
  dsimp only [rawClean]
  have hlen : (List.ofFn (fun i : Fin k => decide (i.val ≤ s.val) :: List.ofFn (fun z : Fin d =>
      decide (i.val < s.val) || (decide (i.val = s.val) && x z)))).flatten.length = k * (d + 1) :=
    flatten_ofFn_length _ (fun _ => by simp)
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]; rfl

private theorem rawClean_true (d k : ℕ) (s : Fin k) (x : Fin d → Bool) :
    (rawClean d k s x).getD (k * (d + 1) + 1) false = true := by
  dsimp only [rawClean]
  have hlen : (List.ofFn (fun i : Fin k => decide (i.val ≤ s.val) :: List.ofFn (fun z : Fin d =>
      decide (i.val < s.val) || (decide (i.val = s.val) && x z)))).flatten.length = k * (d + 1) :=
    flatten_ofFn_length _ (fun _ => by simp)
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
  have : k * (d + 1) + 1 - k * (d + 1) = 1 := by omega
  rw [this]; rfl

-- Step 1: Shared b-inverter phase decoder: b NOT gates + 4*(2^b - 1 - b) positive gates
private theorem append_fold_gates {N : ℕ} {I : Type} (inp : I → List Bool)
    (hinp : ∀ y, (inp y).length = N + 2)
    (htrue : ∀ y, (inp y).getD (N + 1) false = true)
    (q : ℕ) (hq : 0 < q) (ph : I → ℕ) (hph : ∀ y, ph y < 2 * q)
    (gs0 : List Gate) (hctx0 : Ctx N gs0)
    (M : Fin (2 * q) → ℕ) (hM_lt : ∀ r, M r < N + 2 + gs0.length)
    (notMq : ℕ) (hnotMq_lt : notMq < N + 2 + gs0.length)
    (hM_ev : ∀ y (r : Fin (2 * q)), (run gs0 (inp y)).getD (M r) false = decide (r.val ≤ ph y))
    (hnot_ev : ∀ y, (run gs0 (inp y)).getD notMq false = !decide (q ≤ ph y)) :
    ∀ m ≤ q - 1,
      ∃ (ext : List Gate) (F : Fin (m + 1) → ℕ),
        Ctx N (gs0 ++ ext) ∧
        PEqualNP.NotBracket.notCount ⟨ext, 0⟩ = 0 ∧
        ext.length = 2 * m ∧
        (∀ r, F r < N + 2 + (gs0 ++ ext).length) ∧
        ∀ y (r : Fin (m + 1)), (run (gs0 ++ ext) (inp y)).getD (F r) false = decide (r.val ≤ ph y % q) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], fun _ => N + 1, by simpa using hctx0, by simp [PEqualNP.NotBracket.notCount], by simp,
      fun _ => by dsimp only; rw [List.append_nil]; omega, fun y r => ?_⟩
    have hr0 : r.val = 0 := Nat.lt_one_iff.mp r.isLt
    rw [List.append_nil, hr0, run_input gs0 (inp y) (N + 1) (by rw [hinp y]; omega), htrue y]; simp
  | succ m ih =>
    intro hm
    obtain ⟨ext1, F1, hctx1, hnot1, hlen1, hF1_lt, hF1_ev⟩ := ih (by omega)
    let gs1 := gs0 ++ ext1
    let r1 : Fin (2 * q) := ⟨m + 1, by omega⟩
    let r2 : Fin (2 * q) := ⟨q + (m + 1), by omega⟩
    let g1 : Gate := ⟨.and, [M r1, notMq]⟩
    let w1 : ℕ := N + 2 + gs1.length
    let g2 : Gate := ⟨.or, [w1, M r2]⟩
    let w2 : ℕ := N + 2 + gs1.length + 1
    let ext2 := ext1 ++ [g1, g2]
    have hgs2 : gs0 ++ ext2 = (gs1 ++ [g1]) ++ [g2] := by simp [ext2, gs1, List.append_assoc]
    have hctx_mid : Ctx N (gs1 ++ [g1]) := ctx_snoc N gs1 g1 hctx1 (by simp [g1])
      (by intro w hw; simp [g1] at hw; rcases hw with rfl | rfl <;> [have := hM_lt r1; have := hnotMq_lt] <;> simp [gs1] <;> omega)
    have hctx2 : Ctx N (gs0 ++ ext2) := by
      rw [hgs2]; refine ctx_snoc N (gs1 ++ [g1]) g2 hctx_mid (by simp [g2]) ?_
      intro w hw; simp [g2] at hw; rcases hw with rfl | rfl
      · simp [w1]
      · have := hM_lt r2; simp [gs1]; omega
    have hnot2 : PEqualNP.NotBracket.notCount ⟨ext2, 0⟩ = 0 := by
      dsimp only [ext2]; rw [notCount_append, hnot1]; simp [PEqualNP.NotBracket.notCount, g1, g2]
    let F2 : Fin (m + 2) → ℕ := fun r => if h : r.val < m + 1 then F1 ⟨r.val, h⟩ else w2
    refine ⟨ext2, F2, hctx2, hnot2, by simp [ext2, hlen1]; omega, ?_, ?_⟩
    · intro r; dsimp only [F2]
      split_ifs with h
      · have h1 := hF1_lt ⟨r.val, h⟩
        simp only [ext2, List.length_append, List.length_cons, List.length_nil] at h1 ⊢; omega
      · simp only [w2, gs1, ext2, List.length_append, List.length_cons, List.length_nil]; omega
    · intro y r; dsimp only [F2]
      split_ifs with h
      · have hlt := hF1_lt ⟨r.val, h⟩
        have hpref : (run (gs0 ++ ext2) (inp y)).getD (F1 ⟨r.val, h⟩) false =
            (run gs1 (inp y)).getD (F1 ⟨r.val, h⟩) false := by
          rw [show gs0 ++ ext2 = gs1 ++ [g1, g2] by simp [ext2, gs1, List.append_assoc]]
          exact run_prefix gs1 [g1, g2] (inp y) _ (by rw [hinp y]; exact hlt)
        rw [hpref]; exact hF1_ev y ⟨r.val, h⟩
      · have hreq : r.val = m + 1 := by have := r.isLt; omega
        rw [hreq, hgs2, run_snoc]
        have hrlen1 : (run (gs1 ++ [g1]) (inp y)).length = w2 := by
          rw [run_length, hinp y, List.length_append, List.length_singleton]; dsimp [w2]; omega
        rw [← hrlen1, getD_append_eq, orEval]
        simp only [g2, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        have hw1_ev : (run (gs1 ++ [g1]) (inp y)).getD w1 false = (decide (m + 1 ≤ ph y) && !decide (q ≤ ph y)) := by
          rw [run_snoc]
          have hrlen0 : (run gs1 (inp y)).length = w1 := by rw [run_length, hinp y]
          rw [← hrlen0, getD_append_eq, andEval]
          simp only [g1, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          have e1 : (run gs1 (inp y)).getD (M r1) false = decide (m + 1 ≤ ph y) := by
            dsimp only [gs1]; rw [run_prefix gs0 ext1 (inp y) _ (by rw [hinp y]; exact hM_lt r1)]; exact hM_ev y r1
          have e2 : (run gs1 (inp y)).getD notMq false = !decide (q ≤ ph y) := by
            dsimp only [gs1]; rw [run_prefix gs0 ext1 (inp y) _ (by rw [hinp y]; exact hnotMq_lt)]; exact hnot_ev y
          rw [e1, e2]
        have hr2_ev : (run (gs1 ++ [g1]) (inp y)).getD (M r2) false = decide (q + (m + 1) ≤ ph y) := by
          rw [show gs1 ++ [g1] = gs0 ++ (ext1 ++ [g1]) by simp [gs1, List.append_assoc]]
          rw [run_prefix gs0 (ext1 ++ [g1]) (inp y) _ (by rw [hinp y]; exact hM_lt r2)]
          exact hM_ev y r2
        rw [hw1_ev, hr2_ev]
        have hphy := hph y
        by_cases hltq : ph y < q
        · have hmod : ph y % q = ph y := Nat.mod_eq_of_lt hltq
          rw [hmod]
          simp [show ¬ (q ≤ ph y) by omega, show ¬ (q + (m + 1) ≤ ph y) by omega]
        · have hmod : ph y % q = ph y - q := by
            have := Nat.mod_eq_sub_mod (show q ≤ ph y by omega)
            rw [this, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]
          simp only [show q ≤ ph y by omega, decide_true, Bool.not_true, Bool.and_false, Bool.false_or]
          exact decide_eq_decide.mpr (by omega)

private theorem append_unfold_gates {N : ℕ} {I : Type} (inp : I → List Bool)
    (hinp : ∀ y, (inp y).length = N + 2)
    (hfalse : ∀ y, (inp y).getD N false = false)
    (q : ℕ) (hq : 0 < q) (ph : I → ℕ) (hph : ∀ y, ph y < 2 * q)
    (gs0 : List Gate) (hctx0 : Ctx N gs0)
    (notMq : ℕ) (hnotMq_lt : notMq < N + 2 + gs0.length)
    (invF : Fin q → ℕ) (hinvF_lt : ∀ r, invF r < N + 2 + gs0.length)
    (hnot_ev : ∀ y, (run gs0 (inp y)).getD notMq false = !decide (q ≤ ph y))
    (hinvF_ev : ∀ y (r : Fin q), (run gs0 (inp y)).getD (invF r) false = !decide (r.val ≤ ph y % q)) :
    ∀ m ≤ q - 1,
      ∃ (ext : List Gate) (lo hi : Fin (m + 1) → ℕ),
        Ctx N (gs0 ++ ext) ∧
        PEqualNP.NotBracket.notCount ⟨ext, 0⟩ = 0 ∧
        ext.length = 2 * m ∧
        (∀ r, lo r < N + 2 + (gs0 ++ ext).length) ∧
        (∀ r, hi r < N + 2 + (gs0 ++ ext).length) ∧
        (∀ y (r : Fin (m + 1)), (run (gs0 ++ ext) (inp y)).getD (lo r) false = !decide (r.val ≤ ph y)) ∧
        (∀ y (r : Fin (m + 1)), (run (gs0 ++ ext) (inp y)).getD (hi r) false = !decide (q + r.val ≤ ph y)) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], fun _ => N, fun _ => notMq, by simpa using hctx0, by simp [PEqualNP.NotBracket.notCount], by simp,
      fun _ => by dsimp only; rw [List.append_nil]; omega, fun _ => by simpa using hnotMq_lt, ?_, ?_⟩
    · intro y r
      dsimp only
      have hr0 : r.val = 0 := Nat.lt_one_iff.mp r.isLt
      rw [List.append_nil, hr0, run_input gs0 (inp y) N (by rw [hinp y]; omega), hfalse y]; simp
    · intro y r
      dsimp only
      have hr0 : r.val = 0 := Nat.lt_one_iff.mp r.isLt
      rw [List.append_nil, hr0, Nat.add_zero]; exact hnot_ev y
  | succ m ih =>
    intro hm
    obtain ⟨ext1, lo1, hi1, hctx1, hnot1, hlen1, hlo1_lt, hhi1_lt, hlo1_ev, hhi1_ev⟩ := ih (by omega)
    let gs1 := gs0 ++ ext1
    let r1 : Fin q := ⟨m + 1, by omega⟩
    let g1 : Gate := ⟨.and, [notMq, invF r1]⟩
    let g2 : Gate := ⟨.or, [notMq, invF r1]⟩
    let w1 : ℕ := N + 2 + gs1.length
    let w2 : ℕ := N + 2 + gs1.length + 1
    let ext2 := ext1 ++ [g1, g2]
    have hgs2 : gs0 ++ ext2 = (gs1 ++ [g1]) ++ [g2] := by simp [ext2, gs1, List.append_assoc]
    have hctx_mid : Ctx N (gs1 ++ [g1]) := ctx_snoc N gs1 g1 hctx1 (by simp [g1])
      (by intro w hw; simp [g1] at hw; rcases hw with rfl | rfl <;> [have := hnotMq_lt; have := hinvF_lt r1] <;> simp [gs1] <;> omega)
    have hctx2 : Ctx N (gs0 ++ ext2) := by
      rw [hgs2]; refine ctx_snoc N (gs1 ++ [g1]) g2 hctx_mid (by simp [g2]) ?_
      intro w hw; simp [g2] at hw; rcases hw with rfl | rfl <;> [have := hnotMq_lt; have := hinvF_lt r1] <;> simp [gs1] <;> omega
    have hnot2 : PEqualNP.NotBracket.notCount ⟨ext2, 0⟩ = 0 := by
      dsimp only [ext2]; rw [notCount_append, hnot1]; simp [PEqualNP.NotBracket.notCount, g1, g2]
    let lo2 : Fin (m + 2) → ℕ := fun r => if h : r.val < m + 1 then lo1 ⟨r.val, h⟩ else w1
    let hi2 : Fin (m + 2) → ℕ := fun r => if h : r.val < m + 1 then hi1 ⟨r.val, h⟩ else w2
    refine ⟨ext2, lo2, hi2, hctx2, hnot2, by simp [ext2, hlen1]; omega, ?_, ?_, ?_, ?_⟩
    · intro r; dsimp only [lo2]; split_ifs with h
      · have h1 := hlo1_lt ⟨r.val, h⟩
        simp only [ext2, List.length_append, List.length_cons, List.length_nil] at h1 ⊢; omega
      · simp only [w1, gs1, ext2, List.length_append, List.length_cons, List.length_nil]; omega
    · intro r; dsimp only [hi2]; split_ifs with h
      · have h1 := hhi1_lt ⟨r.val, h⟩
        simp only [ext2, List.length_append, List.length_cons, List.length_nil] at h1 ⊢; omega
      · simp only [w2, gs1, ext2, List.length_append, List.length_cons, List.length_nil]; omega
    · intro y r; dsimp only [lo2]; split_ifs with h
      · have hlt := hlo1_lt ⟨r.val, h⟩
        rw [show gs0 ++ ext2 = gs1 ++ [g1, g2] by simp [ext2, gs1, List.append_assoc]]
        rw [run_prefix gs1 [g1, g2] (inp y) _ (by rw [hinp y]; exact hlt)]
        exact hlo1_ev y ⟨r.val, h⟩
      · have hreq : r.val = m + 1 := by have := r.isLt; omega
        rw [hreq, hgs2, run_prefix (gs1 ++ [g1]) [g2] (inp y) w1 (by rw [hinp y, List.length_append, List.length_singleton]; dsimp [w1]; omega)]
        rw [run_snoc]
        have hrlen0 : (run gs1 (inp y)).length = w1 := by rw [run_length, hinp y]
        rw [← hrlen0, getD_append_eq, andEval]
        simp only [g1, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have e1 : (run gs1 (inp y)).getD notMq false = !decide (q ≤ ph y) := by
          dsimp only [gs1]; rw [run_prefix gs0 ext1 (inp y) _ (by rw [hinp y]; exact hnotMq_lt)]; exact hnot_ev y
        have e2 : (run gs1 (inp y)).getD (invF r1) false = !decide (m + 1 ≤ ph y % q) := by
          dsimp only [gs1]; rw [run_prefix gs0 ext1 (inp y) _ (by rw [hinp y]; exact hinvF_lt r1)]; exact hinvF_ev y r1
        rw [e1, e2]
        have hphy := hph y
        by_cases hltq : ph y < q
        · rw [Nat.mod_eq_of_lt hltq]; simp [show ¬ (q ≤ ph y) by omega]
        · simp [show q ≤ ph y by omega, show m + 1 ≤ ph y by omega]
    · intro y r; dsimp only [hi2]; split_ifs with h
      · have hlt := hhi1_lt ⟨r.val, h⟩
        rw [show gs0 ++ ext2 = gs1 ++ [g1, g2] by simp [ext2, gs1, List.append_assoc]]
        rw [run_prefix gs1 [g1, g2] (inp y) _ (by rw [hinp y]; exact hlt)]
        exact hhi1_ev y ⟨r.val, h⟩
      · have hreq : r.val = m + 1 := by have := r.isLt; omega
        rw [hreq, hgs2, run_snoc]
        have hrlen1 : (run (gs1 ++ [g1]) (inp y)).length = w2 := by
          rw [run_length, hinp y, List.length_append, List.length_singleton]; dsimp [w2]; omega
        rw [← hrlen1, getD_append_eq, orEval]
        simp only [g2, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        have e1 : (run (gs1 ++ [g1]) (inp y)).getD notMq false = !decide (q ≤ ph y) := by
          rw [show gs1 ++ [g1] = gs0 ++ (ext1 ++ [g1]) by simp [gs1, List.append_assoc]]
          rw [run_prefix gs0 (ext1 ++ [g1]) (inp y) _ (by rw [hinp y]; exact hnotMq_lt)]; exact hnot_ev y
        have e2 : (run (gs1 ++ [g1]) (inp y)).getD (invF r1) false = !decide (m + 1 ≤ ph y % q) := by
          rw [show gs1 ++ [g1] = gs0 ++ (ext1 ++ [g1]) by simp [gs1, List.append_assoc]]
          rw [run_prefix gs0 (ext1 ++ [g1]) (inp y) _ (by rw [hinp y]; exact hinvF_lt r1)]; exact hinvF_ev y r1
        rw [e1, e2]
        have hphy := hph y
        by_cases hltq : ph y < q
        · simp [show ¬ (q ≤ ph y) by omega, show ¬ (q + (m + 1) ≤ ph y) by omega]
        · have hmod : ph y % q = ph y - q := by
            have := Nat.mod_eq_sub_mod (show q ≤ ph y by omega)
            rw [this, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]
          simp only [show q ≤ ph y by omega, decide_true, Bool.not_true, Bool.false_or]
          exact congrArg (! ·) (decide_eq_decide.mpr (by omega))

private theorem build_phase_inv {N : ℕ} {I : Type} (inp : I → List Bool)
    (hinp : ∀ y, (inp y).length = N + 2)
    (hfalse : ∀ y, (inp y).getD N false = false)
    (htrue : ∀ y, (inp y).getD (N + 1) false = true) :
    ∀ (b : ℕ) (ph : I → ℕ), (∀ y, ph y < 2 ^ b) →
      ∀ (gs0 : List Gate), Ctx N gs0 →
      ∀ (M : Fin (2 ^ b) → ℕ), (∀ r, M r < N + 2 + gs0.length) →
      (∀ y (r : Fin (2 ^ b)), (run gs0 (inp y)).getD (M r) false = decide (r.val ≤ ph y)) →
      ∃ (ext : List Gate) (invW : Fin (2 ^ b) → ℕ),
        Ctx N (gs0 ++ ext) ∧
        PEqualNP.NotBracket.notCount ⟨ext, 0⟩ = b ∧
        ext.length - PEqualNP.NotBracket.notCount ⟨ext, 0⟩ = 4 * (2 ^ b - 1 - b) ∧
        (∀ r, invW r < N + 2 + (gs0 ++ ext).length) ∧
        ∀ y (r : Fin (2 ^ b)), (run (gs0 ++ ext) (inp y)).getD (invW r) false = !decide (r.val ≤ ph y) := by
  intro b
  induction b with
  | zero =>
    intro ph _ gs0 hctx0 _ _ _
    refine ⟨[], fun _ => N, by simpa using hctx0, by simp [PEqualNP.NotBracket.notCount], by simp,
      fun _ => by dsimp only; rw [List.append_nil]; omega, fun y r => ?_⟩
    have hr0 : r.val = 0 := Nat.lt_one_iff.mp r.isLt
    rw [List.append_nil, hr0, run_input gs0 (inp y) N (by rw [hinp y]; omega), hfalse y]; simp
  | succ b ih =>
    intro ph hph gs0 hctx0 M hM_lt hM_ev
    set q := 2 ^ b with hq_def
    have hq_pos : 0 < q := Nat.two_pow_pos b
    have h2q : 2 ^ (b + 1) = 2 * q := by rw [Nat.pow_succ, Nat.mul_comm]
    -- Cast M to Fin (2 * q)
    let M' : Fin (2 * q) → ℕ := fun r => M ⟨r.val, by omega⟩
    have hM'_lt : ∀ r : Fin (2 * q), M' r < N + 2 + gs0.length := fun r => hM_lt ⟨r.val, by omega⟩
    have hM'_ev : ∀ y (r : Fin (2 * q)), (run gs0 (inp y)).getD (M' r) false = decide (r.val ≤ ph y) :=
      fun y r => hM_ev y ⟨r.val, by omega⟩
    -- Step A: 1 NOT gate on M' q
    let mqIdx : Fin (2 * q) := ⟨q, by omega⟩
    let gnot : Gate := ⟨.not, [M' mqIdx]⟩
    let notMq : ℕ := N + 2 + gs0.length
    let gsA := gs0 ++ [gnot]
    have hctxA : Ctx N gsA := ctx_snoc N gs0 gnot hctx0 (by simp [gnot])
      (by intro w hw; simp [gnot] at hw; subst hw; exact hM'_lt mqIdx)
    have hnotMq_ev : ∀ y, (run gsA (inp y)).getD notMq false = !decide (q ≤ ph y) := fun y => by
      dsimp only [gsA]; rw [run_snoc]
      have hrlen : (run gs0 (inp y)).length = notMq := by rw [run_length, hinp y]
      rw [← hrlen, getD_append_eq]
      simp only [gnot, List.map_cons, List.map_nil, notEval_cons]
      exact congrArg (! ·) (hM'_ev y mqIdx)
    have hM'_evA : ∀ y (r : Fin (2 * q)), (run gsA (inp y)).getD (M' r) false = decide (r.val ≤ ph y) := fun y r => by
      dsimp only [gsA]; rw [run_prefix gs0 [gnot] (inp y) _ (by rw [hinp y]; exact hM'_lt r)]; exact hM'_ev y r
    -- Step B: fold gates (2*(q-1) positive gates)
    obtain ⟨extB, F', hctxB, hnotB, hlenB, hF'_lt, hF'_ev⟩ :=
      append_fold_gates inp hinp htrue q hq_pos ph (fun y => by have := hph y; omega) gsA hctxA
        M' (fun r => by have := hM'_lt r; simp [gsA]; omega) notMq (by simp [notMq, gsA])
        hM'_evA hnotMq_ev (q - 1) le_rfl
    let F : Fin q → ℕ := fun r => F' ⟨r.val, by omega⟩
    have hF_lt : ∀ r : Fin q, F r < N + 2 + (gsA ++ extB).length := fun r => hF'_lt ⟨r.val, by omega⟩
    have hF_ev : ∀ y (r : Fin q), (run (gsA ++ extB) (inp y)).getD (F r) false = decide (r.val ≤ ph y % q) :=
      fun y r => hF'_ev y ⟨r.val, by omega⟩
    -- Step C: IH on b with ph % q
    obtain ⟨extC, invF, hctxC, hnotC, hposC, hinvF_lt, hinvF_ev⟩ :=
      ih (fun y => ph y % q) (fun y => Nat.mod_lt _ hq_pos) (gsA ++ extB) hctxB F hF_lt hF_ev
    have hnotMq_ltC : notMq < N + 2 + ((gsA ++ extB) ++ extC).length := by
      dsimp only [notMq, gsA]; simp only [List.length_append, List.length_singleton]; omega
    have hnotMq_evC : ∀ y, (run ((gsA ++ extB) ++ extC) (inp y)).getD notMq false = !decide (q ≤ ph y) := fun y => by
      rw [show (gsA ++ extB) ++ extC = gsA ++ (extB ++ extC) by simp [List.append_assoc]]
      rw [run_prefix gsA (extB ++ extC) (inp y) notMq (by rw [hinp y]; simp [notMq, gsA])]
      exact hnotMq_ev y
    -- Step D: unfold gates (2*(q-1) positive gates)
    obtain ⟨extD, lo, hi, hctxD, hnotD, hlenD, hlo_lt, hhi_lt, hlo_ev, hhi_ev⟩ :=
      append_unfold_gates inp hinp hfalse q hq_pos ph (fun y => by have := hph y; omega)
        ((gsA ++ extB) ++ extC) hctxC notMq hnotMq_ltC invF hinvF_lt hnotMq_evC hinvF_ev (q - 1) le_rfl
    let ext := [gnot] ++ extB ++ extC ++ extD
    have hgs_eq : gs0 ++ ext = ((gsA ++ extB) ++ extC) ++ extD := by simp [ext, gsA, List.append_assoc]
    have hnot_ext : PEqualNP.NotBracket.notCount ⟨ext, 0⟩ = b + 1 := by
      dsimp only [ext]
      rw [notCount_append, notCount_append, notCount_append, hnotB, hnotC, hnotD]
      simp [PEqualNP.NotBracket.notCount, gnot]; omega
    have hpos_ext : ext.length - PEqualNP.NotBracket.notCount ⟨ext, 0⟩ = 4 * (2 ^ (b + 1) - 1 - (b + 1)) := by
      have hncC_le := notCount_le_len extC
      have hlen_ext : ext.length = 1 + extB.length + extC.length + extD.length := by simp [ext]; omega
      have hb_le : b < q := Nat.lt_two_pow_self
      rw [hnot_ext, hlen_ext, hlenB, hlenD]
      omega
    let invW : Fin (2 ^ (b + 1)) → ℕ := fun r =>
      if h : r.val < q then lo ⟨r.val, by omega⟩ else hi ⟨r.val - q, by omega⟩
    refine ⟨ext, invW, by rw [hgs_eq]; exact hctxD, hnot_ext, hpos_ext, ?_, ?_⟩
    · intro r; dsimp only [invW]; rw [hgs_eq]
      split_ifs with h
      · exact hlo_lt ⟨r.val, by omega⟩
      · exact hhi_lt ⟨r.val - q, by omega⟩
    · intro y r; dsimp only [invW]; rw [hgs_eq]
      split_ifs with h
      · exact hlo_ev y ⟨r.val, by omega⟩
      · have h1 := hhi_ev y ⟨r.val - q, by omega⟩
        have hadd : q + (r.val - q) = r.val := by omega
        simpa [hadd] using h1

-- Step 2: Data-bit multiplexer for a single (j, z): 2*(q-1) positive gates, 0 NOT gates
private theorem build_mux_one (d b h : ℕ) (hh : 0 < h)
    (j : Fin h) (z : Fin d)
    (gs0 : List Gate) (hctx0 : Ctx (2 ^ b * h * (d + 1)) gs0)
    (invW : Fin (2 ^ b) → ℕ) (hinvW_lt : ∀ r, invW r < 2 ^ b * h * (d + 1) + 2 + gs0.length)
    (hinvW_ev : ∀ (s : Fin (2 ^ b * h)) (x : Fin d → Bool) (r : Fin (2 ^ b)),
      (run gs0 (rawClean d (2 ^ b * h) s x)).getD (invW r) false = !decide (r.val ≤ s.val / h)) :
    ∀ m ≤ 2 ^ b - 1,
      ∃ (ext : List Gate) (w : ℕ),
        Ctx (2 ^ b * h * (d + 1)) (gs0 ++ ext) ∧
        PEqualNP.NotBracket.notCount ⟨ext, 0⟩ = 0 ∧
        ext.length = 2 * m ∧
        w < 2 ^ b * h * (d + 1) + 2 + (gs0 ++ ext).length ∧
        ∀ (s : Fin (2 ^ b * h)) (x : Fin d → Bool), s.val % h = j.val →
          (run (gs0 ++ ext) (rawClean d (2 ^ b * h) s x)).getD w false =
            if s.val / h = 2 ^ b - 1 ∨ s.val / h < m then x z else false := by
  let q := 2 ^ b
  have hq_pos : 0 < q := Nat.two_pow_pos b
  let k := q * h
  let N := k * (d + 1)
  intro m
  induction m with
  | zero =>
    intro _
    let idx0 : Fin k := ⟨(q - 1) * h + j.val, by
      have : (q - 1) * h + h = q * h := by rw [← Nat.add_one_mul]; congr 1; omega
      have := j.isLt; omega⟩
    let w0 : ℕ := idx0.val * (d + 1) + 1 + z.val
    have hw0_lt : w0 < N := by
      have : (idx0.val + 1) * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt idx0.isLt)
      rw [Nat.add_mul, Nat.one_mul] at this; have := z.isLt; omega
    refine ⟨[], w0, by simpa using hctx0, by simp [PEqualNP.NotBracket.notCount], by simp,
      by dsimp only [N, k, q] at hw0_lt; rw [List.append_nil]; omega, fun s x hmod => ?_⟩
    rw [List.append_nil, run_input gs0 _ w0 (by rw [rawClean_length]; dsimp only [N, k, q] at hw0_lt; omega)]
    have hdata := rawClean_data d k s x idx0 z
    change (rawClean d k s x).getD w0 false = _
    rw [hdata]
    have hs_decomp : s.val = (s.val / h) * h + j.val := by
      have := Nat.div_add_mod s.val h; rw [hmod, Nat.mul_comm] at this; omega
    have hdiv_lt : s.val / h < q := Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq s.isLt (Nat.mul_comm _ _))
    have hnotlt : ¬ (idx0.val < s.val) := by
      dsimp only [idx0]
      have : s.val / h ≤ q - 1 := by omega
      have hmul : (s.val / h) * h ≤ (q - 1) * h := Nat.mul_le_mul_right h this
      omega
    have heq_iff : idx0.val = s.val ↔ s.val / h = q - 1 := by
      dsimp only [idx0]
      constructor
      · intro heq
        have : (q - 1) * h = (s.val / h) * h := by omega
        exact (Nat.mul_right_cancel hh this).symm
      · intro heq; rw [hs_decomp, heq]
    simp only [hnotlt, decide_false, Bool.false_or, Nat.not_lt_zero, or_false]
    by_cases hp : s.val / h = q - 1
    · rw [if_pos hp, decide_eq_true (heq_iff.mpr hp), Bool.true_and]
    · rw [if_neg hp, decide_eq_false (fun h => hp (heq_iff.mp h)), Bool.false_and]
  | succ m ih =>
    intro hm
    obtain ⟨ext1, w_acc, hctx1, hnot1, hlen1, hw_acc_lt, hw_acc_ev⟩ := ih (by omega)
    let gs1 := gs0 ++ ext1
    let idxm : Fin k := ⟨m * h + j.val, by
      have : m * h + h ≤ q * h := by rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right h (by omega)
      have := j.isLt; omega⟩
    let um : ℕ := idxm.val * (d + 1) + 1 + z.val
    have hum_lt : um < N := by
      have : (idxm.val + 1) * (d + 1) ≤ k * (d + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt idxm.isLt)
      rw [Nat.add_mul, Nat.one_mul] at this; have := z.isLt; omega
    let r_next : Fin q := ⟨m + 1, by omega⟩
    let g1 : Gate := ⟨.and, [um, invW r_next]⟩
    let w1 : ℕ := N + 2 + gs1.length
    let g2 : Gate := ⟨.or, [w_acc, w1]⟩
    let w2 : ℕ := N + 2 + gs1.length + 1
    let ext2 := ext1 ++ [g1, g2]
    have hgs2 : gs0 ++ ext2 = (gs1 ++ [g1]) ++ [g2] := by simp [ext2, gs1, List.append_assoc]
    have hctx_mid : Ctx N (gs1 ++ [g1]) := ctx_snoc N gs1 g1 hctx1 (by simp [g1])
      (by intro w hw; simp [g1] at hw; rcases hw with rfl | rfl
          · omega
          · have h1 := hinvW_lt r_next; dsimp only [N, k, q, gs1] at h1 ⊢; rw [List.length_append]; omega)
    have hctx2 : Ctx N (gs0 ++ ext2) := by
      rw [hgs2]; refine ctx_snoc N (gs1 ++ [g1]) g2 hctx_mid (by simp [g2]) ?_
      intro w hw; simp [g2] at hw; rcases hw with rfl | rfl
      · dsimp only [N, k, q, gs1] at hw_acc_lt ⊢; rw [List.length_append, List.length_singleton]; omega
      · simp [w1]
    have hnot2 : PEqualNP.NotBracket.notCount ⟨ext2, 0⟩ = 0 := by
      dsimp only [ext2]; rw [notCount_append, hnot1]; simp [PEqualNP.NotBracket.notCount, g1, g2]
    refine ⟨ext2, w2, hctx2, hnot2, by simp [ext2, hlen1]; omega,
      by dsimp only [w2, gs1, ext2, N, k, q]; simp only [List.length_append, List.length_cons, List.length_nil]; omega, ?_⟩
    intro s x hmod
    rw [hgs2, run_snoc]
    have hrlen1 : (run (gs1 ++ [g1]) (rawClean d k s x)).length = w2 := by
      rw [run_length, rawClean_length, List.length_append, List.length_singleton]; dsimp [w2, N, k]; omega
    rw [← hrlen1, getD_append_eq, orEval]
    simp only [g2, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    have hacc : (run (gs1 ++ [g1]) (rawClean d k s x)).getD w_acc false =
        if s.val / h = q - 1 ∨ s.val / h < m then x z else false := by
      rw [run_prefix gs1 [g1] _ w_acc (by rw [rawClean_length]; exact hw_acc_lt)]
      exact hw_acc_ev s x hmod
    have hw1_ev : (run (gs1 ++ [g1]) (rawClean d k s x)).getD w1 false =
        ((decide (idxm.val < s.val) || (decide (idxm.val = s.val) && x z)) && !decide (m + 1 ≤ s.val / h)) := by
      rw [run_snoc]
      have hrlen0 : (run gs1 (rawClean d k s x)).length = w1 := by rw [run_length, rawClean_length]
      rw [← hrlen0, getD_append_eq, andEval]
      simp only [g1, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      have e1 : (run gs1 (rawClean d k s x)).getD um false =
          (decide (idxm.val < s.val) || (decide (idxm.val = s.val) && x z)) := by
        rw [run_input gs1 _ um (by rw [rawClean_length]; omega)]
        exact rawClean_data d k s x idxm z
      have e2 : (run gs1 (rawClean d k s x)).getD (invW r_next) false = !decide (m + 1 ≤ s.val / h) := by
        dsimp only [gs1]; rw [run_prefix gs0 ext1 _ _ (by rw [rawClean_length]; exact hinvW_lt r_next)]
        exact hinvW_ev s x r_next
      rw [e1, e2]
    rw [hacc, hw1_ev]
    have hs_decomp : s.val = (s.val / h) * h + j.val := by
      have := Nat.div_add_mod s.val h; rw [hmod, Nat.mul_comm] at this; omega
    have hdiv_lt : s.val / h < q := Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq s.isLt (Nat.mul_comm _ _))
    rcases lt_trichotomy (s.val / h) m with hlt | heq | hgt
    · have hgt_idx : s.val < idxm.val := by
        dsimp only [idxm]
        have : (s.val / h + 1) * h ≤ m * h := Nat.mul_le_mul_right h (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; omega
      rw [if_pos (Or.inr hlt), if_pos (Or.inr (by omega))]
      simp [show ¬ (idxm.val < s.val) by omega, show idxm.val ≠ s.val by omega]
    · have heq_idx : idxm.val = s.val := by dsimp only [idxm]; rw [hs_decomp, heq]
      rw [if_neg (by omega), if_pos (Or.inr (by omega))]
      simp [heq_idx, show ¬ (m + 1 ≤ s.val / h) by omega]
    · have hge : m + 1 ≤ s.val / h := by omega
      simp only [hge, decide_true, Bool.not_true, Bool.and_false, Bool.or_false]
      by_cases hlast : s.val / h = q - 1
      · rw [if_pos (Or.inl hlast), if_pos (Or.inl hlast)]
      · rw [if_neg (by omega), if_neg (by omega)]

-- Build all d mux wires for a single position j: 2*d*(q-1) positive gates
private theorem build_mux_row (d b h : ℕ) (hh : 0 < h) (j : Fin h)
    (gs0 : List Gate) (hctx0 : Ctx (2 ^ b * h * (d + 1)) gs0)
    (invW : Fin (2 ^ b) → ℕ) (hinvW_lt : ∀ r, invW r < 2 ^ b * h * (d + 1) + 2 + gs0.length)
    (hinvW_ev : ∀ (s : Fin (2 ^ b * h)) (x : Fin d → Bool) (r : Fin (2 ^ b)),
      (run gs0 (rawClean d (2 ^ b * h) s x)).getD (invW r) false = !decide (r.val ≤ s.val / h)) :
    ∀ m (hm : m ≤ d),
      ∃ (ext : List Gate) (X : Fin m → ℕ),
        Ctx (2 ^ b * h * (d + 1)) (gs0 ++ ext) ∧
        PEqualNP.NotBracket.notCount ⟨ext, 0⟩ = 0 ∧
        ext.length = 2 * m * (2 ^ b - 1) ∧
        (∀ z, X z < 2 ^ b * h * (d + 1) + 2 + (gs0 ++ ext).length) ∧
        ∀ (s : Fin (2 ^ b * h)) (x : Fin d → Bool) (z : Fin m), s.val % h = j.val →
          (run (gs0 ++ ext) (rawClean d (2 ^ b * h) s x)).getD (X z) false = x ⟨z.val, lt_of_lt_of_le z.isLt hm⟩ := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], fun z => Fin.elim0 z, by simpa using hctx0, by simp [PEqualNP.NotBracket.notCount], by simp,
      fun z => Fin.elim0 z, fun _ _ z => Fin.elim0 z⟩
  | succ m ih =>
    intro hm
    obtain ⟨ext1, X1, hctx1, hnot1, hlen1, hX1_lt, hX1_ev⟩ := ih (by omega)
    have hinvW_lt1 : ∀ r, invW r < 2 ^ b * h * (d + 1) + 2 + (gs0 ++ ext1).length := fun r => by
      have := hinvW_lt r; simp; omega
    have hinvW_ev1 : ∀ (s : Fin (2 ^ b * h)) (x : Fin d → Bool) (r : Fin (2 ^ b)),
        (run (gs0 ++ ext1) (rawClean d (2 ^ b * h) s x)).getD (invW r) false = !decide (r.val ≤ s.val / h) :=
      fun s x r => by
        rw [run_prefix gs0 ext1 _ _ (by rw [rawClean_length]; exact hinvW_lt r)]
        exact hinvW_ev s x r
    obtain ⟨ext2, wm, hctx2, hnot2, hlen2, hwm_lt, hwm_ev⟩ :=
      build_mux_one d b h hh j ⟨m, by omega⟩ (gs0 ++ ext1) hctx1 invW hinvW_lt1 hinvW_ev1 (2 ^ b - 1) le_rfl
    let ext := ext1 ++ ext2
    have hgs_eq : gs0 ++ ext = (gs0 ++ ext1) ++ ext2 := by simp [ext, List.append_assoc]
    let X2 : Fin (m + 1) → ℕ := fun z => if hlt : z.val < m then X1 ⟨z.val, hlt⟩ else wm
    refine ⟨ext, X2, by rw [hgs_eq]; exact hctx2,
      by dsimp only [ext]; rw [notCount_append, hnot1, hnot2],
      by dsimp only [ext]; rw [List.length_append, hlen1, hlen2]; ring, ?_, ?_⟩
    · intro z; dsimp only [X2]; rw [hgs_eq]
      split_ifs with hlt
      · have h1 := hX1_lt ⟨z.val, hlt⟩; simp only [List.length_append] at h1 ⊢; omega
      · exact hwm_lt
    · intro s x z hmod; dsimp only [X2]; rw [hgs_eq]
      split_ifs with hlt
      · rw [run_prefix (gs0 ++ ext1) ext2 _ _ (by rw [rawClean_length]; exact hX1_lt ⟨z.val, hlt⟩)]
        exact hX1_ev s x ⟨z.val, hlt⟩ hmod
      · have hzm : z.val = m := by have := z.isLt; omega
        have h1 := hwm_ev s x hmod
        have hdiv_lt : s.val / h < 2 ^ b := Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq s.isLt (Nat.mul_comm _ _))
        have hcond : s.val / h = 2 ^ b - 1 ∨ s.val / h < 2 ^ b - 1 := by omega
        rw [if_pos hcond] at h1
        have hfin : (⟨m, by omega⟩ : Fin d) = ⟨z.val, lt_of_lt_of_le z.isLt hm⟩ := Fin.ext hzm.symm
        rwa [hfin] at h1

-- Build all h*d mux wires: 2*d*h*(q-1) positive gates
private theorem build_mux_all (d b h : ℕ) (hh : 0 < h)
    (gs0 : List Gate) (hctx0 : Ctx (2 ^ b * h * (d + 1)) gs0)
    (invW : Fin (2 ^ b) → ℕ) (hinvW_lt : ∀ r, invW r < 2 ^ b * h * (d + 1) + 2 + gs0.length)
    (hinvW_ev : ∀ (s : Fin (2 ^ b * h)) (x : Fin d → Bool) (r : Fin (2 ^ b)),
      (run gs0 (rawClean d (2 ^ b * h) s x)).getD (invW r) false = !decide (r.val ≤ s.val / h)) :
    ∀ m ≤ h,
      ∃ (ext : List Gate) (X : Fin m → Fin d → ℕ),
        Ctx (2 ^ b * h * (d + 1)) (gs0 ++ ext) ∧
        PEqualNP.NotBracket.notCount ⟨ext, 0⟩ = 0 ∧
        ext.length = 2 * d * m * (2 ^ b - 1) ∧
        (∀ j z, X j z < 2 ^ b * h * (d + 1) + 2 + (gs0 ++ ext).length) ∧
        ∀ (s : Fin (2 ^ b * h)) (x : Fin d → Bool) (j : Fin m) (z : Fin d), s.val % h = j.val →
          (run (gs0 ++ ext) (rawClean d (2 ^ b * h) s x)).getD (X j z) false = x z := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], fun j => Fin.elim0 j, by simpa using hctx0, by simp [PEqualNP.NotBracket.notCount], by simp,
      fun j => Fin.elim0 j, fun _ _ j => Fin.elim0 j⟩
  | succ m ih =>
    intro hm
    obtain ⟨ext1, X1, hctx1, hnot1, hlen1, hX1_lt, hX1_ev⟩ := ih (by omega)
    have hinvW_lt1 : ∀ r, invW r < 2 ^ b * h * (d + 1) + 2 + (gs0 ++ ext1).length := fun r => by
      have := hinvW_lt r; simp; omega
    have hinvW_ev1 : ∀ (s : Fin (2 ^ b * h)) (x : Fin d → Bool) (r : Fin (2 ^ b)),
        (run (gs0 ++ ext1) (rawClean d (2 ^ b * h) s x)).getD (invW r) false = !decide (r.val ≤ s.val / h) :=
      fun s x r => by
        rw [run_prefix gs0 ext1 _ _ (by rw [rawClean_length]; exact hinvW_lt r)]
        exact hinvW_ev s x r
    obtain ⟨ext2, Xm, hctx2, hnot2, hlen2, hXm_lt, hXm_ev⟩ :=
      build_mux_row d b h hh ⟨m, by omega⟩ (gs0 ++ ext1) hctx1 invW hinvW_lt1 hinvW_ev1 d le_rfl
    let ext := ext1 ++ ext2
    have hgs_eq : gs0 ++ ext = (gs0 ++ ext1) ++ ext2 := by simp [ext, List.append_assoc]
    let X2 : Fin (m + 1) → Fin d → ℕ := fun j z => if hlt : j.val < m then X1 ⟨j.val, hlt⟩ z else Xm z
    refine ⟨ext, X2, by rw [hgs_eq]; exact hctx2,
      by dsimp only [ext]; rw [notCount_append, hnot1, hnot2],
      by dsimp only [ext]; rw [List.length_append, hlen1, hlen2]; ring, ?_, ?_⟩
    · intro j z; dsimp only [X2]; rw [hgs_eq]
      split_ifs with hlt
      · have h1 := hX1_lt ⟨j.val, hlt⟩ z; simp only [List.length_append] at h1 ⊢; omega
      · exact hXm_lt z
    · intro s x j z hmod; dsimp only [X2]; rw [hgs_eq]
      split_ifs with hlt
      · rw [run_prefix (gs0 ++ ext1) ext2 _ _ (by rw [rawClean_length]; exact hX1_lt ⟨j.val, hlt⟩ z)]
        exact hX1_ev s x ⟨j.val, hlt⟩ z hmod
      · have hjm : j.val = m := by have := j.isLt; omega
        exact hXm_ev s x z (by rw [hmod, hjm])

-- Step 3: Append a remapped copy of circuit A
private def remapWire (d N base : ℕ) (inW : Fin d → ℕ) (w : ℕ) : ℕ :=
  if h : w < d then inW ⟨w, h⟩
  else if w = d then N
  else if w = d + 1 then N + 1
  else base + (w - (d + 2))

private def remapGate (d N base : ℕ) (inW : Fin d → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapWire d N base inW)⟩

private theorem append_copy_A {d N : ℕ} (A : Circuit)
    (hfanA : PEqualNP.MetaComplexity.FanInTwo A)
    (hrbA : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) A)
    (gs0 : List Gate) (hctx0 : Ctx N gs0)
    (inW : Fin d → ℕ) (hinW_lt : ∀ z, inW z < N + 2 + gs0.length) :
    let base := N + 2 + gs0.length
    let copy := A.gates.map (remapGate d N base inW)
    Ctx N (gs0 ++ copy) ∧
    copy.length = A.size ∧
    PEqualNP.NotBracket.notCount ⟨copy, 0⟩ = PEqualNP.NotBracket.notCount A ∧
    (∀ w < d + 2 + A.size, remapWire d N base inW w < N + 2 + (gs0 ++ copy).length) ∧
    ∀ (inp : List Bool) (x : Fin d → Bool),
      inp.length = N + 2 →
      inp.getD N false = false →
      inp.getD (N + 1) false = true →
      (∀ z : Fin d, (run gs0 inp).getD (inW z) false = x z) →
      ∀ w < d + 2 + A.size,
        (run (gs0 ++ copy) inp).getD (remapWire d N base inW w) false =
        (run A.gates (List.ofFn x ++ [false, true])).getD w false := by
  intro base copy
  have hcopy_len : copy.length = A.size := by simp [copy, Circuit.size]
  have hcopy_not : PEqualNP.NotBracket.notCount ⟨copy, 0⟩ = PEqualNP.NotBracket.notCount A := by
    letI : DecidableEq GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
    dsimp only [PEqualNP.NotBracket.notCount, copy]
    have hgen : ∀ (L : List Gate),
        ((L.map (remapGate d N base inW)).filter (fun g => decide (g.op = .not))).length =
        (L.filter (fun g => decide (g.op = .not))).length := by
      intro L; induction L with
      | nil => simp
      | cons g gs ih =>
        simp only [List.map_cons, List.filter_cons, remapGate]
        cases h : g.op <;> simp [h, ih]
    exact hgen A.gates
  have hctx : Ctx N (gs0 ++ copy) := by
    refine ⟨?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact hctx0.1 g h1
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h2
        obtain ⟨hop, hlen⟩ := hfanA g0 hg0
        exact ⟨hop, by simp [remapGate]; exact hlen⟩
    · intro i hi w hw
      rw [List.length_append, hcopy_len] at hi
      by_cases hlt : i < gs0.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD] at hw
        exact hctx0.2 i hlt w hw
      · let m := i - gs0.length
        have hm_lt : m < A.gates.length := by dsimp [Circuit.size] at hi; omega
        have hi_eq : i = gs0.length + m := by omega
        have hge : (gs0 ++ copy).getD i ⟨.or, []⟩ = remapGate d N base inW (A.gates[m]) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
          have hsub : i - gs0.length = m := by omega
          rw [hsub]
          dsimp only [copy]
          rw [List.getElem?_map, List.getElem?_eq_getElem hm_lt]; rfl
        rw [hge] at hw
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
        have hu_lt : u < d + 2 + m :=
          hrbA m hm_lt u (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem _ _ hm_lt]; exact hu)
        dsimp only [remapWire]
        split_ifs with h1 h2 h3
        · have := hinW_lt ⟨u, h1⟩; omega
        · omega
        · omega
        · dsimp only [base]; omega
  have hremap_lt : ∀ w < d + 2 + A.size, remapWire d N base inW w < N + 2 + (gs0 ++ copy).length := by
    intro w hw
    rw [List.length_append, hcopy_len]
    dsimp only [remapWire, base]
    split_ifs with h1 h2 h3
    · have := hinW_lt ⟨w, h1⟩; omega
    · omega
    · omega
    · omega
  refine ⟨hctx, hcopy_len, hcopy_not, hremap_lt, ?_⟩
  intro inp x hinp hfalse htrue hinW_ev w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases h1 : w < d
    · dsimp only [remapWire]; rw [dif_pos h1]
      rw [run_prefix gs0 copy inp (inW ⟨w, h1⟩) (by rw [hinp]; exact hinW_lt ⟨w, h1⟩), hinW_ev ⟨w, h1⟩]
      rw [run_input A.gates _ w (by simp; omega)]
      rw [getD_append_left _ _ _ _ (by simp [h1]), List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h1]; rfl
    · by_cases h2 : w = d
      · dsimp only [remapWire]; rw [dif_neg h1, if_pos h2]
        rw [run_input (gs0 ++ copy) inp N (by rw [hinp]; omega), hfalse]
        rw [run_input A.gates _ w (by simp; omega), h2]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
      · by_cases h3 : w = d + 1
        · dsimp only [remapWire]; rw [dif_neg h1, if_neg h2, if_pos h3]
          rw [run_input (gs0 ++ copy) inp (N + 1) (by rw [hinp]; omega), htrue]
          rw [run_input A.gates _ w (by simp; omega), h3]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
          have : d + 1 - (List.ofFn x).length = 1 := by simp
          rw [this]; rfl
        · -- Gate w = d + 2 + m
          let m := w - (d + 2)
          have hw_eq : w = d + 2 + m := by omega
          have hm_lt : m < A.gates.length := by dsimp [Circuit.size] at hw; omega
          have hrw : remapWire d N base inW w = N + 2 + (gs0.length + m) := by
            dsimp only [remapWire, base]; rw [dif_neg h1, if_neg h2, if_neg h3]; omega
          rw [hrw]
          have hidx_lt : gs0.length + m < (gs0 ++ copy).length := by rw [List.length_append, hcopy_len]; dsimp [Circuit.size]; omega
          have hrgC := run_gate (gs0 ++ copy) inp (gs0.length + m) hidx_lt
          rw [hinp] at hrgC
          have hrgA := run_gate A.gates (List.ofFn x ++ [false, true]) m hm_lt
          have hAlen : (List.ofFn x ++ [false, true]).length = d + 2 := by simp
          rw [hAlen, ← hw_eq] at hrgA
          rw [hrgC, hrgA]
          have hgel : (gs0 ++ copy)[gs0.length + m]'hidx_lt = remapGate d N base inW (A.gates[m]'hm_lt) := by
            rw [List.getElem_append_right (by omega)]
            simp only [Nat.add_sub_cancel_left, copy, List.getElem_map]
          rw [hgel]
          dsimp only [remapGate]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro u hu
          have hu_lt : u < d + 2 + m :=
            hrbA m hm_lt u (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem _ _ hm_lt]; exact hu)
          have hru_lt : remapWire d N base inW u < N + 2 + (gs0.length + m) := by
            dsimp only [remapWire, base]
            split_ifs with hu1 hu2 hu3
            · have := hinW_lt ⟨u, hu1⟩; omega
            · omega
            · omega
            · omega
          have hu_lt_w : u < w := by omega
          simp only [Function.comp_apply, if_pos hru_lt, if_pos hu_lt_w]
          exact ih u hu_lt_w (by dsimp [Circuit.size]; omega)

-- Append h copies of A (one per position j : Fin h)
private theorem append_all_copies (d t b h : ℕ) (hh : 0 < h)
    (A : Circuit) (out : Fin t → ℕ)
    (hfanA : PEqualNP.MetaComplexity.FanInTwo A)
    (hrbA : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) A)
    (hout : ∀ a, out a < d + 2 + A.size)
    (gs0 : List Gate) (hctx0 : Ctx (2 ^ b * h * (d + 1)) gs0)
    (X : Fin h → Fin d → ℕ)
    (hX_lt : ∀ j z, X j z < 2 ^ b * h * (d + 1) + 2 + gs0.length)
    (hX_ev : ∀ (s : Fin (2 ^ b * h)) (x : Fin d → Bool) (j : Fin h) (z : Fin d), s.val % h = j.val →
      (run gs0 (rawClean d (2 ^ b * h) s x)).getD (X j z) false = x z) :
    ∀ m ≤ h,
      ∃ (ext : List Gate) (tap : Fin m → Fin t → ℕ),
        Ctx (2 ^ b * h * (d + 1)) (gs0 ++ ext) ∧
        ext.length = m * A.size ∧
        PEqualNP.NotBracket.notCount ⟨ext, 0⟩ = m * PEqualNP.NotBracket.notCount A ∧
        (∀ j a, tap j a < 2 ^ b * h * (d + 1) + 2 + (gs0 ++ ext).length) ∧
        ∀ (s : Fin (2 ^ b * h)) (x : Fin d → Bool) (j : Fin m) (a : Fin t), s.val % h = j.val →
          (run (gs0 ++ ext) (rawClean d (2 ^ b * h) s x)).getD (tap j a) false =
          (run A.gates (List.ofFn x ++ [false, true])).getD (out a) false := by
  set N := 2 ^ b * h * (d + 1)
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], fun j => Fin.elim0 j, by simpa using hctx0, by simp, by simp [PEqualNP.NotBracket.notCount],
      fun j => Fin.elim0 j, fun _ _ j => Fin.elim0 j⟩
  | succ m ih =>
    intro hm
    obtain ⟨ext1, tap1, hctx1, hlen1, hnot1, htap1_lt, htap1_ev⟩ := ih (by omega)
    let gs1 := gs0 ++ ext1
    let jm : Fin h := ⟨m, by omega⟩
    let base := N + 2 + gs1.length
    have hXm_lt : ∀ z, X jm z < N + 2 + gs1.length := fun z => by
      have := hX_lt jm z; simp [gs1]; omega
    obtain ⟨hctx2, hcopy_len, hcopy_not, hremap_lt, hcopy_ev⟩ :=
      append_copy_A (d := d) (N := N) A hfanA hrbA gs1 hctx1 (X jm) hXm_lt
    let copy := A.gates.map (remapGate d N base (X jm))
    let ext := ext1 ++ copy
    have hgs_eq : gs0 ++ ext = gs1 ++ copy := by simp [ext, gs1, List.append_assoc]
    let tap2 : Fin (m + 1) → Fin t → ℕ := fun j a =>
      if hlt : j.val < m then tap1 ⟨j.val, hlt⟩ a else remapWire d N base (X jm) (out a)
    refine ⟨ext, tap2, by rw [hgs_eq]; exact hctx2,
      by dsimp only [ext]; rw [List.length_append, hlen1, hcopy_len]; ring,
      by dsimp only [ext]; rw [notCount_append, hnot1, hcopy_not]; ring, ?_, ?_⟩
    · intro j a; dsimp only [tap2]; rw [hgs_eq]
      split_ifs with hlt
      · have h1 := htap1_lt ⟨j.val, hlt⟩ a; simp only [gs1, List.length_append] at h1 ⊢; omega
      · exact hremap_lt (out a) (hout a)
    · intro s x j a hmod; dsimp only [tap2]; rw [hgs_eq]
      split_ifs with hlt
      · rw [run_prefix gs1 copy _ _ (by rw [rawClean_length]; exact htap1_lt ⟨j.val, hlt⟩ a)]
        exact htap1_ev s x ⟨j.val, hlt⟩ a hmod
      · have hjm : j.val = m := by have := j.isLt; omega
        exact hcopy_ev (rawClean d (2 ^ b * h) s x) x
          (rawClean_length d (2 ^ b * h) s x)
          (rawClean_false d (2 ^ b * h) s x)
          (rawClean_true d (2 ^ b * h) s x)
          (fun z => by
            dsimp only [gs1]; rw [run_prefix gs0 ext1 _ _ (by rw [rawClean_length]; exact hX_lt jm z)]
            exact hX_ev s x jm z (by rw [hmod, hjm]))
          (out a) (hout a)

private theorem main_clean (d t b h : ℕ) (hh : 0 < h)
    (A : Circuit) (out : Fin t → ℕ)
    (hfanA : PEqualNP.MetaComplexity.FanInTwo A)
    (hrbA : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) A)
    (hout : ∀ a, out a < d + 2 + A.size) :
    let q := 2 ^ b
    let k := q * h
    let N := k * (d + 1)
    ∃ (C : Circuit) (tap : Fin h → Fin t → ℕ),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + 2) C ∧
      C.output < N + 2 + C.size ∧
      (∀ j a, tap j a < N + 2 + C.size) ∧
      PEqualNP.NotBracket.notCount C ≤ b + h * PEqualNP.NotBracket.notCount A ∧
      C.size - PEqualNP.NotBracket.notCount C ≤
        h * (A.size - PEqualNP.NotBracket.notCount A) + (2 * d * h) * (q - 1) + 4 * (q - 1 - b) ∧
      ∀ (s : Fin k) (x : Fin d → Bool) (a : Fin t),
        (C.wires (rawClean d k s x)).getD (tap ⟨s.val % h, Nat.mod_lt _ hh⟩ a) false =
        (A.wires (List.ofFn x ++ [false, true])).getD (out a) false := by
  dsimp only
  set q := 2 ^ b
  set k := q * h
  set N := k * (d + 1)
  -- Phase markers M r = raw wire (r * h) * (d + 1)
  let M : Fin q → ℕ := fun r => (r.val * h) * (d + 1)
  have hM_lt : ∀ r : Fin q, M r < N + 2 + ([] : List Gate).length := fun r => by
    have h1 : r.val * h < k := by
      have : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    have h2 : (r.val * h) * (d + 1) < k * (d + 1) := Nat.mul_lt_mul_of_pos_right h1 (Nat.zero_lt_succ d)
    simp [M, N]; omega
  have hM_ev : ∀ (y : Fin k × (Fin d → Bool)) (r : Fin q),
      (run [] (rawClean d k y.1 y.2)).getD (M r) false = decide (r.val ≤ y.1.val / h) := by
    intro ⟨s, x⟩ r
    have hrh_lt : r.val * h < k := by
      have : (r.val + 1) * h ≤ q * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt r.isLt)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    dsimp only [run, List.foldl_nil, M]
    have hm := rawClean_marker d k s x ⟨r.val * h, hrh_lt⟩
    dsimp only at hm; rw [hm]
    exact decide_eq_decide.mpr ⟨fun hle => (Nat.le_div_iff_mul_le hh).mpr hle, fun hle => (Nat.le_div_iff_mul_le hh).mp hle⟩
  -- Stage 1: shared inverter decoder
  obtain ⟨ext1, invW, hctx1, hnot1, hpos1, hinvW_lt, hinvW_ev⟩ :=
    build_phase_inv (N := N) (I := Fin k × (Fin d → Bool))
      (fun y => rawClean d k y.1 y.2)
      (fun y => rawClean_length d k y.1 y.2)
      (fun y => rawClean_false d k y.1 y.2)
      (fun y => rawClean_true d k y.1 y.2)
      b (fun y => y.1.val / h)
      (fun y => Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact y.1.isLt))
      [] (ctx_nil N) M hM_lt hM_ev
  rw [List.nil_append] at hctx1 hinvW_lt hinvW_ev
  -- Stage 2: data-bit multiplexers
  obtain ⟨ext2, X, hctx2, hnot2, hlen2, hX_lt, hX_ev⟩ :=
    build_mux_all d b h hh ext1 hctx1 invW hinvW_lt (fun s x r => hinvW_ev (s, x) r) h le_rfl
  -- Stage 3: h copies of A
  obtain ⟨ext3, tap, hctx3, hlen3, hnot3, htap_lt, htap_ev⟩ :=
    append_all_copies d t b h hh A out hfanA hrbA hout (ext1 ++ ext2) hctx2 X hX_lt hX_ev h le_rfl
  let gs := (ext1 ++ ext2) ++ ext3
  let C : Circuit := ⟨gs, 0⟩
  have hnotC : PEqualNP.NotBracket.notCount C = b + h * PEqualNP.NotBracket.notCount A := by
    dsimp only [C, gs]
    rw [notCount_append, notCount_append, hnot1, hnot2, hnot3]; omega
  have hposC : C.size - PEqualNP.NotBracket.notCount C =
      h * (A.size - PEqualNP.NotBracket.notCount A) + (2 * d * h) * (q - 1) + 4 * (q - 1 - b) := by
    have hA_le : PEqualNP.NotBracket.notCount A ≤ A.size := notCount_le_len A.gates
    have h1_le : b ≤ ext1.length := by rw [← hnot1]; exact notCount_le_len ext1
    have hpos1' : ext1.length - b = 4 * (2 ^ b - 1 - b) := by rwa [hnot1] at hpos1
    have hsz : C.size = ext1.length + ext2.length + ext3.length := by
      simp only [C, gs, Circuit.size, List.length_append]
    have hmul_sub : h * (A.size - PEqualNP.NotBracket.notCount A) =
        h * A.size - h * PEqualNP.NotBracket.notCount A := Nat.mul_sub_left_distrib h _ _
    have hle_mul : h * PEqualNP.NotBracket.notCount A ≤ h * A.size := Nat.mul_le_mul_left h hA_le
    dsimp only [q] at *
    rw [hsz, hnotC, hlen2, hlen3, hmul_sub]
    omega
  refine ⟨C, tap, ?_, ?_, by dsimp [C, Circuit.size]; omega, htap_lt, by omega, by omega, ?_⟩
  · intro g hg; obtain ⟨ho, hl⟩ := hctx3.1 g hg
    exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩
  · intro idx hidx w hw
    dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt, C] at hw
    rw [List.getD_eq_getElem _ _ hidx] at hw
    exact hctx3.2 idx hidx w (by rw [List.getD_eq_getElem _ _ hidx]; exact hw)
  · intro s x a
    change (run gs (rawClean d k s x)).getD (tap ⟨s.val % h, Nat.mod_lt _ hh⟩ a) false =
      (run A.gates (List.ofFn x ++ [false, true])).getD (out a) false
    exact htap_ev s x ⟨s.val % h, Nat.mod_lt _ hh⟩ a rfl

end PEqualNP.Outside.L_lib_1330

theorem PEqualNP.Outside.L_lib_1330 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (d t b h : Nat) (hh : 0 < h),
      let q := 2^b
      let k := q*h
      let N := k*(d+1)
      let raw := fun (s : Fin k) (x : Fin d → Bool) =>
        (List.ofFn (fun i : Fin k => decide (i ≤ s) :: List.ofFn (fun z : Fin d =>
          decide (i < s) || (decide (i=s) && x z)))).flatten ++ [false,true]
      let valid := fun (r : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) C ∧
        C.output < r+2+C.size
      ∀ (A : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin t → Nat),
        valid d A → (∀ a, out a < d+2+A.size) →
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin h → Fin t → Nat),
          valid N C ∧ (∀ j a, tap j a < N+2+C.size) ∧
          PEqualNP.NotBracket.notCount C ≤ b+h*PEqualNP.NotBracket.notCount A ∧
          C.size - PEqualNP.NotBracket.notCount C ≤
            h*(A.size-PEqualNP.NotBracket.notCount A) + (2*d*h)*(q-1) + 4*(q-1-b) ∧
          ∀ (s : Fin k) (x : Fin d → Bool) (a : Fin t),
            (C.wires (raw s x)).getD (tap ⟨s.val % h, Nat.mod_lt _ hh⟩ a) false =
            (A.wires (List.ofFn x ++ [false,true])).getD (out a) false := by
  dsimp only
  intro d t b h hh A out ⟨hfanA, hrbA, _⟩ hout
  obtain ⟨C, tap, h1, h2, h3, h4, h5, h6, h7⟩ :=
    PEqualNP.Outside.L_lib_1330.main_clean d t b h hh A out hfanA hrbA hout
  refine ⟨C, tap, ⟨h1, h2, h3⟩, h4, h5, h6, ?_⟩
  intro s x a
  have hraw_eq :
      (List.ofFn (fun i : Fin (2 ^ b * h) =>
        @decide (i ≤ s) (Classical.propDecidable _) :: List.ofFn (fun z : Fin d =>
          @decide (i < s) (Classical.propDecidable _) || (@decide (i = s) (Classical.propDecidable _) && x z)))).flatten ++ [false, true] =
      PEqualNP.Outside.L_lib_1330.rawClean d (2 ^ b * h) s x := by
    dsimp only [PEqualNP.Outside.L_lib_1330.rawClean]
    apply congrArg (· ++ [false, true])
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    have hle : @decide (i ≤ s) (Classical.propDecidable _) = decide (i.val ≤ s.val) :=
      decide_eq_decide.mpr Fin.le_def
    have hlt : @decide (i < s) (Classical.propDecidable _) = decide (i.val < s.val) :=
      decide_eq_decide.mpr Fin.lt_def
    have heq : @decide (i = s) (Classical.propDecidable _) = decide (i.val = s.val) :=
      decide_eq_decide.mpr Fin.ext_iff
    rw [hle, hlt, heq]
  rw [hraw_eq]
  exact h7 s x a
