import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29767

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents Classical

private def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

private def depths (width : ℕ) (C : Circuit) : List ℕ :=
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)

private def fits (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin q → ℕ),
    ReadsBack (n + m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n + m) C).getD (tap j) 0 ≤ 1 ∧
      Represents (G j) ⟨C.gates, tap j⟩

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> revert h <;> decide

private theorem zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t
  decide

private theorem b2z_decide_ne_zero (t : ZMod 2) : b2z (decide (t ≠ 0)) = t := by
  revert t
  decide

private theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private theorem b2z_mod2 (c : ℕ) : b2z ((c % 2) == 1) = (c : ZMod 2) := by
  have hmod : c % 2 = 0 ∨ c % 2 = 1 := Nat.mod_two_eq_zero_or_one c
  rcases hmod with h | h
  · rw [h]
    have h0 : (c : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff c 2).2 (Nat.dvd_of_mod_eq_zero h)
    rw [h0]
    rfl
  · rw [h]
    have h1 : (c : ZMod 2) = 1 := by
      have hc : c = 2 * (c / 2) + 1 := by omega
      rw [hc]
      push_cast
      have h2 : (2 : ZMod 2) = 0 := rfl
      rw [h2]
      simp
    rw [h1]
    rfl

private def runFold {α : Type} (step : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun l g => l ++ [step l g]) init

private theorem runFold_length {α : Type} (step : List α → Gate → α) (init : List α) (gs : List Gate) :
    (runFold step init gs).length = init.length + gs.length := by
  unfold runFold
  induction gs generalizing init with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private theorem runFold_append {α : Type} (step : List α → Gate → α) (init : List α)
    (gs1 gs2 : List Gate) :
    runFold step init (gs1 ++ gs2) = runFold step (runFold step init gs1) gs2 := by
  unfold runFold
  exact List.foldl_append

private theorem getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d0 : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d0 = l1.getD i d0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem runFold_getD_prefix {α : Type} (step : List α → Gate → α) (init : List α)
    (gs : List Gate) (w : ℕ) (d0 : α) (hw : w < init.length) :
    (runFold step init gs).getD w d0 = init.getD w d0 := by
  unfold runFold
  induction gs generalizing init with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hw' : w < (init ++ [step init g]).length := by
      rw [List.length_append, List.length_singleton]; omega
    rw [ih (init ++ [step init g]) hw', getD_append_left _ _ _ _ hw]

private theorem runFold_getD_gate {α : Type} (step : List α → Gate → α) (init : List α)
    (gs : List Gate) (idx : ℕ) (hidx : idx < gs.length) (d0 : α) :
    (runFold step init gs).getD (init.length + idx) d0 =
      step (runFold step init (gs.take idx)) (gs[idx]) := by
  have hsplit : gs = gs.take idx ++ [gs[idx]] ++ gs.drop (idx + 1) := by
    conv_lhs => rw [← List.take_append_drop idx gs]
    rw [List.append_assoc, List.singleton_append]
    congr 1
    exact (List.cons_getElem_drop_succ (h := hidx)).symm
  conv_lhs => rw [hsplit]
  rw [runFold_append, runFold_append]
  have hlen_take : (runFold step init (gs.take idx)).length = init.length + idx := by
    rw [runFold_length, List.length_take, min_eq_left (le_of_lt hidx)]
  have hlen1 : init.length + idx < (runFold step (runFold step init (gs.take idx)) [gs[idx]]).length := by
    rw [runFold_length, hlen_take, List.length_singleton]; omega
  rw [runFold_getD_prefix step _ (gs.drop (idx + 1)) (init.length + idx) d0 hlen1]
  unfold runFold
  simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
  have heq : init.length + idx = (gs.take idx |>.foldl (fun l g => l ++ [step l g]) init).length :=
    hlen_take.symm
  rw [List.getElem?_append_right (le_of_eq heq.symm), Nat.sub_eq_zero_of_le (le_of_eq heq)]
  rfl

private theorem wires_eq_runFold (C : Circuit) (x : List Bool) :
    C.wires x = runFold (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) x C.gates :=
  rfl

private theorem depths_eq_runFold (width : ℕ) (C : Circuit) :
    depths width C = runFold (fun ds g =>
      (g.inputs.map fun a => ds.getD a 0).foldr max 0 + (nonlinear g).toNat)
      (List.replicate width 0) C.gates :=
  rfl

private theorem oneEach_length {n m : ℕ} (a : Fin n) (b : Fin m) :
    (oneEach a b).length = n + m := by
  simp [oneEach]

private theorem oneEach_getD_left {n m : ℕ} (a : Fin n) (b : Fin m) (w : ℕ) (hw : w < n) :
    (oneEach a b).getD w false = decide ((⟨w, hw⟩ : Fin n) = a) := by
  unfold oneEach
  rw [getD_append_left _ _ _ _ (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem oneEach_getD_right {n m : ℕ} (a : Fin n) (b : Fin m) (w : ℕ)
    (hlo : n ≤ w) (hhi : w < n + m) :
    (oneEach a b).getD w false = decide ((⟨w - n, by omega⟩ : Fin m) = b) := by
  unfold oneEach
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [hlo])]
  simp only [List.length_ofFn]
  have hlt : w - n < m := by omega
  simp [hlt]

private theorem gateAt_eq_getElem (C : Circuit) (idx : ℕ) (hidx : idx < C.gates.length) :
    gateAt C idx = C.gates[idx] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hidx]

private theorem wires_getD_gate {n m : ℕ} (C : Circuit) (hRB : ReadsBack (n + m) C)
    (a : Fin n) (b : Fin m) (idx : ℕ) (hidx : idx < C.gates.length) :
    (C.wires (oneEach a b)).getD (n + m + idx) false =
      C.gates[idx].op.eval (C.gates[idx].inputs.map fun i => (C.wires (oneEach a b)).getD i false) := by
  rw [wires_eq_runFold]
  have hlen : (oneEach a b).length = n + m := oneEach_length a b
  have h1 := runFold_getD_gate (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    (oneEach a b) C.gates idx hidx false
  rw [hlen] at h1
  rw [h1]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hlt : i < n + m + idx := by
    have hrb := hRB idx hidx i
    rw [gateAt_eq_getElem C idx hidx] at hrb
    exact hrb hi
  have htake : C.gates = C.gates.take idx ++ C.gates.drop idx := (List.take_append_drop idx C.gates).symm
  conv_rhs => rw [htake, runFold_append]
  have hlt2 : i < (runFold (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
      (oneEach a b) (C.gates.take idx)).length := by
    rw [runFold_length, hlen, List.length_take, min_eq_left (le_of_lt hidx)]
    exact hlt
  exact (runFold_getD_prefix _ _ (C.gates.drop idx) i false hlt2).symm

private theorem depths_getD_gate {n m : ℕ} (C : Circuit) (hRB : ReadsBack (n + m) C)
    (idx : ℕ) (hidx : idx < C.gates.length) :
    (depths (n + m) C).getD (n + m + idx) 0 =
      (C.gates[idx].inputs.map fun i => (depths (n + m) C).getD i 0).foldr max 0 +
        (nonlinear C.gates[idx]).toNat := by
  rw [depths_eq_runFold]
  have hlen : (List.replicate (n + m) 0).length = n + m := List.length_replicate
  have h1 := runFold_getD_gate (fun ds g =>
      (g.inputs.map fun a => ds.getD a 0).foldr max 0 + (nonlinear g).toNat)
    (List.replicate (n + m) 0) C.gates idx hidx 0
  rw [hlen] at h1
  rw [h1]
  congr 2
  refine List.map_congr_left fun i hi => ?_
  have hlt : i < n + m + idx := by
    have hrb := hRB idx hidx i
    rw [gateAt_eq_getElem C idx hidx] at hrb
    exact hrb hi
  have htake : C.gates = C.gates.take idx ++ C.gates.drop idx := (List.take_append_drop idx C.gates).symm
  conv_rhs => rw [htake, runFold_append]
  have hlt2 : i < (runFold (fun ds g =>
      (g.inputs.map fun a => ds.getD a 0).foldr max 0 + (nonlinear g).toNat)
      (List.replicate (n + m) 0) (C.gates.take idx)).length := by
    rw [runFold_length, hlen, List.length_take, min_eq_left (le_of_lt hidx)]
    exact hlt
  exact (runFold_getD_prefix _ _ (C.gates.drop idx) i 0 hlt2).symm

private theorem depths_getD_input (width : ℕ) (C : Circuit) (w : ℕ) (hw : w < width) :
    (depths width C).getD w 0 = 0 := by
  rw [depths_eq_runFold, runFold_getD_prefix _ _ _ w 0 (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

private def GoodCirc (n m : ℕ) (gs : List Gate) : Prop :=
  ReadsBack (n + m) ⟨gs, 0⟩ ∧ ∀ g ∈ gs, g.inputs.length ≤ 2

private def valOf {n m : ℕ} (gs : List Gate) (w : ℕ) (a : Fin n) (b : Fin m) : ZMod 2 :=
  b2z (((Circuit.mk gs 0).wires (oneEach a b)).getD w false)

private def depOf (n m : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  (depths (n + m) ⟨gs, 0⟩).getD w 0

private theorem valOf_append_prefix {n m : ℕ} (gs1 gs2 : List Gate) (w : ℕ)
    (hw : w < n + m + gs1.length) (a : Fin n) (b : Fin m) :
    valOf (gs1 ++ gs2) w a b = valOf gs1 w a b := by
  simp only [valOf, wires_eq_runFold]
  rw [runFold_append]
  have hlen : w < (runFold (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
      (oneEach a b) gs1).length := by
    rw [runFold_length, oneEach_length]; exact hw
  rw [runFold_getD_prefix _ _ gs2 w false hlen]

private theorem depOf_append_prefix (n m : ℕ) (gs1 gs2 : List Gate) (w : ℕ)
    (hw : w < n + m + gs1.length) :
    depOf n m (gs1 ++ gs2) w = depOf n m gs1 w := by
  simp only [depOf, depths_eq_runFold]
  rw [runFold_append]
  have hlen : w < (runFold (fun ds g =>
      (g.inputs.map fun a => ds.getD a 0).foldr max 0 + (nonlinear g).toNat)
      (List.replicate (n + m) 0) gs1).length := by
    rw [runFold_length, List.length_replicate]; exact hw
  rw [runFold_getD_prefix _ _ gs2 w 0 hlen]

private theorem goodCirc_append_gate {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs)
    (g : Gate) (hlen : g.inputs.length ≤ 2) (hin : ∀ i ∈ g.inputs, i < n + m + gs.length) :
    GoodCirc n m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    rw [gateAt_eq_getElem ⟨gs ++ [g], 0⟩ j hj] at hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [List.getElem_append_left hlt] at hi
      have hrb := hgs.1 j hlt i
      rw [gateAt_eq_getElem ⟨gs, 0⟩ j hlt] at hrb
      exact hrb hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [List.getElem_append_right (le_refl _)] at hi
      simp only [Nat.sub_self, List.getElem_cons_zero] at hi
      exact hin i hi
  · intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h2
    · exact hgs.2 g' h1
    · simp only [List.mem_singleton] at h2
      rw [h2]; exact hlen

private theorem append_gate_eval {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs)
    (g : Gate) (hlen : g.inputs.length ≤ 2) (hin : ∀ i ∈ g.inputs, i < n + m + gs.length) :
    let gs' := gs ++ [g]
    let w := n + m + gs.length
    GoodCirc n m gs' ∧
    w < n + m + gs'.length ∧
    gs'.countP nonlinear = gs.countP nonlinear + (nonlinear g).toNat ∧
    depOf n m gs' w = (g.inputs.map (depOf n m gs)).foldr max 0 + (nonlinear g).toNat ∧
    ∀ (a : Fin n) (b : Fin m),
      valOf gs' w a b = b2z (g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires (oneEach a b)).getD i false)) := by
  intro gs' w
  have hgood' : GoodCirc n m gs' := goodCirc_append_gate gs hgs g hlen hin
  have hidx : gs.length < gs'.length := by simp [gs']
  have hget : gs'[gs.length] = g := by simp [gs']
  refine ⟨hgood', by simp [w, gs'], ?_, ?_, ?_⟩
  · simp only [gs', List.countP_append, List.countP_cons, List.countP_nil]
    cases nonlinear g <;> simp
  · have hd := depths_getD_gate ⟨gs', 0⟩ hgood'.1 gs.length hidx
    change (depths (n + m) ⟨gs', 0⟩).getD (n + m + gs.length) 0 = _
    rw [hd, hget]
    congr 2
    refine List.map_congr_left fun i hi => ?_
    exact depOf_append_prefix n m gs [g] i (hin i hi)
  · intro a b
    have hw := wires_getD_gate ⟨gs', 0⟩ hgood'.1 a b gs.length hidx
    change b2z (((Circuit.mk gs' 0).wires (oneEach a b)).getD w false) = _
    rw [hw, hget]
    congr 2
    refine List.map_congr_left fun i hi => ?_
    have hpre := valOf_append_prefix gs [g] i (hin i hi) a b
    exact b2z_inj hpre

private theorem buildConst0 {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs) :
    ∃ (extra : List Gate) (w : ℕ),
      let gs' := gs ++ extra
      GoodCirc n m gs' ∧ w < n + m + gs'.length ∧
      gs'.countP nonlinear = gs.countP nonlinear ∧
      depOf n m gs' w = 0 ∧
      ∀ (a : Fin n) (b : Fin m), valOf gs' w a b = 0 := by
  let g : Gate := ⟨GateOp.or, []⟩
  have hnl : nonlinear g = false := by decide
  obtain ⟨hgood', hwlt, hcnt, hdep, hval⟩ := append_gate_eval gs hgs g (by decide) (by simp [g])
  refine ⟨[g], n + m + gs.length, hgood', hwlt, ?_, ?_, ?_⟩
  · rw [hcnt, hnl]; simp
  · rw [hdep, hnl]; simp [g]
  · intro a b; rw [hval a b]; rfl

private theorem buildXor {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs)
    (x y : ℕ) (hx : x < n + m + gs.length) (hy : y < n + m + gs.length) :
    ∃ (extra : List Gate) (w : ℕ),
      let gs' := gs ++ extra
      GoodCirc n m gs' ∧ w < n + m + gs'.length ∧
      gs'.countP nonlinear = gs.countP nonlinear ∧
      depOf n m gs' w = max (depOf n m gs x) (depOf n m gs y) ∧
      ∀ (a : Fin n) (b : Fin m), valOf gs' w a b = valOf gs x a b + valOf gs y a b := by
  let g1 : Gate := ⟨GateOp.mod 2, [x, y]⟩
  have hnl1 : nonlinear g1 = false := rfl
  obtain ⟨hgood1, hw1lt, hcnt1, hdep1, hval1⟩ := append_gate_eval gs hgs g1 (by simp [g1]) (by
    intro i hi; simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption)
  set gs1 := gs ++ [g1]
  set w1 := n + m + gs.length
  let g2 : Gate := ⟨GateOp.not, [w1]⟩
  have hnl2 : nonlinear g2 = false := rfl
  obtain ⟨hgood2, hw2lt, hcnt2, hdep2, hval2⟩ := append_gate_eval gs1 hgood1 g2 (by simp [g2]) (by
    intro i hi; simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hi]; exact hw1lt)
  refine ⟨[g1, g2], n + m + gs1.length, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [gs1, List.append_assoc] using hgood2
  · simp [gs1]
  · have hEq : gs ++ [g1, g2] = gs1 ++ [g2] := by simp [gs1, List.append_assoc]
    rw [hEq, hcnt2, hcnt1, hnl1, hnl2]; simp
  · have hEq : gs ++ [g1, g2] = gs1 ++ [g2] := by simp [gs1, List.append_assoc]
    rw [hEq, hdep2, hnl2]
    simp only [g2, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false,
      Nat.max_zero, add_zero]
    rw [hdep1, hnl1]
    simp [g1]
  · intro a b
    have hEq : gs ++ [g1, g2] = gs1 ++ [g2] := by simp [gs1, List.append_assoc]
    rw [hEq, hval2 a b]
    have hv1 := hval1 a b
    have hbit1 : ((Circuit.mk gs1 0).wires (oneEach a b)).getD w1 false =
        g1.op.eval [((Circuit.mk gs 0).wires (oneEach a b)).getD x false,
                    ((Circuit.mk gs 0).wires (oneEach a b)).getD y false] :=
      b2z_inj hv1
    simp only [g1, g2, List.map_cons, List.map_nil, hbit1, valOf]
    generalize ((Circuit.mk gs 0).wires (oneEach a b)).getD x false = bx
    generalize ((Circuit.mk gs 0).wires (oneEach a b)).getD y false = by_
    cases bx <;> cases by_ <;> decide

private theorem buildAnd {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs)
    (x y : ℕ) (hx : x < n + m + gs.length) (hy : y < n + m + gs.length) :
    ∃ (extra : List Gate) (w : ℕ),
      let gs' := gs ++ extra
      GoodCirc n m gs' ∧ w < n + m + gs'.length ∧
      gs'.countP nonlinear = gs.countP nonlinear + 1 ∧
      depOf n m gs' w = max (depOf n m gs x) (depOf n m gs y) + 1 ∧
      ∀ (a : Fin n) (b : Fin m), valOf gs' w a b = valOf gs x a b * valOf gs y a b := by
  let g : Gate := ⟨GateOp.and, [x, y]⟩
  have hnl : nonlinear g = true := rfl
  obtain ⟨hgood', hwlt, hcnt, hdep, hval⟩ := append_gate_eval gs hgs g (by simp [g]) (by
    intro i hi; simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption)
  refine ⟨[g], n + m + gs.length, hgood', hwlt, ?_, ?_, ?_⟩
  · rw [hcnt, hnl]; simp
  · rw [hdep, hnl]; simp [g]
  · intro a b
    rw [hval a b]
    simp only [g, List.map_cons, List.map_nil, valOf]
    generalize ((Circuit.mk gs 0).wires (oneEach a b)).getD x false = bx
    generalize ((Circuit.mk gs 0).wires (oneEach a b)).getD y false = by_
    cases bx <;> cases by_ <;> decide

private theorem buildXorList {n m : ℕ} (ws : List ℕ) (dmax : ℕ) :
    ∀ (gs : List Gate), GoodCirc n m gs →
      (∀ i ∈ ws, i < n + m + gs.length ∧ depOf n m gs i ≤ dmax) →
      ∃ (extra : List Gate) (w : ℕ),
        let gs' := gs ++ extra
        GoodCirc n m gs' ∧ w < n + m + gs'.length ∧
        gs'.countP nonlinear = gs.countP nonlinear ∧
        depOf n m gs' w ≤ dmax ∧
        ∀ (a : Fin n) (b : Fin m), valOf gs' w a b = (ws.map (fun i => valOf gs i a b)).sum := by
  induction ws with
  | nil =>
    intro gs hgs _
    obtain ⟨extra, w, hgood', hwlt, hcnt, hdep, hval⟩ := buildConst0 gs hgs
    exact ⟨extra, w, hgood', hwlt, hcnt, by omega, fun a b => by simpa using hval a b⟩
  | cons x rest ih =>
    intro gs hgs hws
    obtain ⟨hx_lt, hx_dep⟩ := hws x (by simp)
    obtain ⟨extra1, w1, hgood1, hw1lt, hcnt1, hdep1, hval1⟩ :=
      ih gs hgs (fun i hi => hws i (by simp [hi]))
    set gs1 := gs ++ extra1
    have hx_lt1 : x < n + m + gs1.length := by
      simp only [gs1, List.length_append]; omega
    obtain ⟨extra2, w2, hgood2, hw2lt, hcnt2, hdep2, hval2⟩ :=
      buildXor gs1 hgood1 x w1 hx_lt1 hw1lt
    refine ⟨extra1 ++ extra2, w2, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [gs1, List.append_assoc] using hgood2
    · simpa [gs1, List.append_assoc] using hw2lt
    · rw [← List.append_assoc, hcnt2, hcnt1]
    · rw [← List.append_assoc, hdep2, depOf_append_prefix n m gs extra1 x hx_lt]
      exact max_le hx_dep hdep1
    · intro a b
      rw [← List.append_assoc, hval2 a b, valOf_append_prefix gs extra1 x hx_lt a b, hval1 a b]
      rfl

private theorem buildSep {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs)
    (α : Fin n → ZMod 2) (β : Fin m → ZMod 2) :
    ∃ (extra : List Gate) (w : ℕ),
      let gs' := gs ++ extra
      GoodCirc n m gs' ∧ w < n + m + gs'.length ∧
      gs'.countP nonlinear = gs.countP nonlinear ∧
      depOf n m gs' w = 0 ∧
      ∀ (a : Fin n) (b : Fin m), valOf gs' w a b = α a + β b := by
  let wsL : List ℕ := ((List.finRange n).filter (fun i => decide (α i = 1))).map Fin.val
  let wsR : List ℕ := ((List.finRange m).filter (fun j => decide (β j = 1))).map (fun j => n + j.val)
  let ws : List ℕ := wsL ++ wsR
  have hws : ∀ i ∈ ws, i < n + m + gs.length ∧ depOf n m gs i ≤ 0 := by
    intro i hi
    rcases List.mem_append.1 hi with hL | hR
    · obtain ⟨k, _, rfl⟩ := List.mem_map.1 hL
      exact ⟨by omega, by rw [depOf, depths_getD_input (n + m) ⟨gs, 0⟩ k.val (by omega)]⟩
    · obtain ⟨k, _, rfl⟩ := List.mem_map.1 hR
      exact ⟨by omega, by rw [depOf, depths_getD_input (n + m) ⟨gs, 0⟩ (n + k.val) (by omega)]⟩
  obtain ⟨extra, w, hgood', hwlt, hcnt, hdep, hval⟩ := buildXorList ws 0 gs hgs hws
  refine ⟨extra, w, hgood', hwlt, hcnt, Nat.eq_zero_of_le_zero hdep, fun a b => ?_⟩
  rw [hval a b]
  simp only [ws, List.map_append, List.sum_append]
  have hLsum : (wsL.map (fun i => valOf gs i a b)).sum = α a := by
    have hmap : wsL.map (fun i => valOf gs i a b) =
        ((List.finRange n).filter (fun i => decide (α i = 1))).map
          (fun i => b2z (decide (i = a))) := by
      simp only [wsL, List.map_map]
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, valOf, wires_eq_runFold]
      rw [runFold_getD_prefix _ _ _ i.val false (by rw [oneEach_length]; omega),
        oneEach_getD_left a b i.val i.isLt]
    rw [hmap]
    have hnodup : ((List.finRange n).filter (fun i => decide (α i = 1))).Nodup :=
      (List.nodup_finRange n).filter _
    have hsum_fin : (((List.finRange n).filter (fun i => decide (α i = 1))).map
        (fun i => b2z (decide (i = a)))).sum =
        ∑ i ∈ ((List.finRange n).filter (fun i => decide (α i = 1))).toFinset,
          b2z (decide (i = a)) := by
      rw [← List.sum_toFinset _ hnodup]
    rw [hsum_fin]
    by_cases ha : α a = 1
    · have hmem : a ∈ ((List.finRange n).filter (fun i => decide (α i = 1))).toFinset := by
        simp [ha]
      rw [Finset.sum_eq_single a]
      · simp [b2z, ha]
      · intro i _ hne; simp [b2z, hne]
      · intro hnot; exact False.elim (hnot hmem)
    · have ha0 : α a = 0 := by rcases zmod2_cases (α a) with h | h; exact h; exact False.elim (ha h)
      have hnot : a ∉ ((List.finRange n).filter (fun i => decide (α i = 1))).toFinset := by
        simp [ha]
      rw [Finset.sum_eq_zero]
      · exact ha0.symm
      · intro i hi
        have hne : i ≠ a := fun heq => hnot (heq ▸ hi)
        simp [b2z, hne]
  have hRsum : (wsR.map (fun i => valOf gs i a b)).sum = β b := by
    have hmap : wsR.map (fun i => valOf gs i a b) =
        ((List.finRange m).filter (fun j => decide (β j = 1))).map
          (fun j => b2z (decide (j = b))) := by
      simp only [wsR, List.map_map]
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply, valOf, wires_eq_runFold]
      rw [runFold_getD_prefix _ _ _ (n + j.val) false (by rw [oneEach_length]; omega),
        oneEach_getD_right a b (n + j.val) (by omega) (by omega)]
      have hfin : (⟨n + j.val - n, by omega⟩ : Fin m) = j := Fin.ext (Nat.add_sub_cancel_left n j.val)
      rw [hfin]
    rw [hmap]
    have hnodup : ((List.finRange m).filter (fun j => decide (β j = 1))).Nodup :=
      (List.nodup_finRange m).filter _
    have hsum_fin : (((List.finRange m).filter (fun j => decide (β j = 1))).map
        (fun j => b2z (decide (j = b)))).sum =
        ∑ j ∈ ((List.finRange m).filter (fun j => decide (β j = 1))).toFinset,
          b2z (decide (j = b)) := by
      rw [← List.sum_toFinset _ hnodup]
    rw [hsum_fin]
    by_cases hb : β b = 1
    · have hmem : b ∈ ((List.finRange m).filter (fun j => decide (β j = 1))).toFinset := by
        simp [hb]
      rw [Finset.sum_eq_single b]
      · simp [b2z, hb]
      · intro j _ hne; simp [b2z, hne]
      · intro hnot; exact False.elim (hnot hmem)
    · have hb0 : β b = 0 := by rcases zmod2_cases (β b) with h | h; exact h; exact False.elim (hb h)
      have hnot : b ∉ ((List.finRange m).filter (fun j => decide (β j = 1))).toFinset := by
        simp [hb]
      rw [Finset.sum_eq_zero]
      · exact hb0.symm
      · intro j hj
        have hne : j ≠ b := fun heq => hnot (heq ▸ hj)
        simp [b2z, hne]
  rw [hLsum, hRsum]

private theorem buildRankPair {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs)
    (u1 u2 : Fin n → ZMod 2) (v1 v2 : Fin m → ZMod 2) :
    ∃ (extra : List Gate) (w : ℕ),
      let gs' := gs ++ extra
      GoodCirc n m gs' ∧ w < n + m + gs'.length ∧
      gs'.countP nonlinear = gs.countP nonlinear + 1 ∧
      depOf n m gs' w ≤ 1 ∧
      ∀ (a : Fin n) (b : Fin m), valOf gs' w a b = u1 a * v1 b + u2 a * v2 b := by
  obtain ⟨ex1, w1, hgood1, hw1lt, hcnt1, hdep1, hval1⟩ := buildSep gs hgs u1 v2
  set gs1 := gs ++ ex1
  obtain ⟨ex2, w2, hgood2, hw2lt, hcnt2, hdep2, hval2⟩ := buildSep gs1 hgood1 u2 v1
  set gs2 := gs1 ++ ex2
  have hw1lt2 : w1 < n + m + gs2.length := by simp only [gs2, List.length_append]; omega
  obtain ⟨ex3, w3, hgood3, hw3lt, hcnt3, hdep3, hval3⟩ := buildAnd gs2 hgood2 w1 w2 hw1lt2 hw2lt
  set gs3 := gs2 ++ ex3
  obtain ⟨ex4, w4, hgood4, hw4lt, hcnt4, hdep4, hval4⟩ :=
    buildSep gs3 hgood3 (fun a => u1 a * u2 a) (fun b => v1 b * v2 b)
  set gs4 := gs3 ++ ex4
  have hw3lt4 : w3 < n + m + gs4.length := by simp only [gs4, List.length_append]; omega
  obtain ⟨ex5, w5, hgood5, hw5lt, hcnt5, hdep5, hval5⟩ := buildXor gs4 hgood4 w3 w4 hw3lt4 hw4lt
  refine ⟨ex1 ++ ex2 ++ ex3 ++ ex4 ++ ex5, w5, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [gs4, gs3, gs2, gs1, List.append_assoc] using hgood5
  · simpa [gs4, gs3, gs2, gs1, List.append_assoc] using hw5lt
  · have hEq : gs ++ (ex1 ++ ex2 ++ ex3 ++ ex4 ++ ex5) = gs4 ++ ex5 := by
      simp [gs4, gs3, gs2, gs1, List.append_assoc]
    rw [hEq, hcnt5, hcnt4, hcnt3, hcnt2, hcnt1]
  · have hEq : gs ++ (ex1 ++ ex2 ++ ex3 ++ ex4 ++ ex5) = gs4 ++ ex5 := by
      simp [gs4, gs3, gs2, gs1, List.append_assoc]
    rw [hEq, hdep5, depOf_append_prefix n m gs3 ex4 w3 hw3lt, hdep3,
      depOf_append_prefix n m gs1 ex2 w1 hw1lt, hdep1, hdep2, hdep4]
    simp
  · intro a b
    have hEq : gs ++ (ex1 ++ ex2 ++ ex3 ++ ex4 ++ ex5) = gs4 ++ ex5 := by
      simp [gs4, gs3, gs2, gs1, List.append_assoc]
    rw [hEq, hval5 a b, valOf_append_prefix gs3 ex4 w3 hw3lt a b, hval3 a b,
      valOf_append_prefix gs1 ex2 w1 hw1lt a b, hval1 a b, hval2 a b, hval4 a b]
    have h2 : (2 : ZMod 2) = 0 := rfl
    linear_combination (u1 a * u2 a + v1 b * v2 b) * h2

private theorem buildRankSum {n m : ℕ} : ∀ (r : ℕ) (u : Fin r → Fin n → ZMod 2) (v : Fin r → Fin m → ZMod 2)
    (gs : List Gate), GoodCirc n m gs →
    ∃ (extra : List Gate) (w : ℕ),
      let gs' := gs ++ extra
      GoodCirc n m gs' ∧ w < n + m + gs'.length ∧
      gs'.countP nonlinear ≤ gs.countP nonlinear + (r + 1) / 2 ∧
      depOf n m gs' w ≤ 1 ∧
      ∀ (a : Fin n) (b : Fin m), valOf gs' w a b = ∑ i : Fin r, u i a * v i b := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro u v gs hgs
    match r with
    | 0 =>
      obtain ⟨extra, w, hgood', hwlt, hcnt, hdep, hval⟩ := buildConst0 gs hgs
      exact ⟨extra, w, hgood', hwlt, by omega, by omega, fun a b => by simpa using hval a b⟩
    | 1 =>
      obtain ⟨extra, w, hgood', hwlt, hcnt, hdep, hval⟩ :=
        buildRankPair gs hgs (u 0) (fun _ => 0) (v 0) (fun _ => 0)
      refine ⟨extra, w, hgood', hwlt, by omega, hdep, fun a b => ?_⟩
      rw [hval a b]
      simp
    | r + 2 =>
      let u' : Fin r → Fin n → ZMod 2 := fun i => u ⟨i.val, by omega⟩
      let v' : Fin r → Fin m → ZMod 2 := fun i => v ⟨i.val, by omega⟩
      obtain ⟨ex1, w1, hgood1, hw1lt, hcnt1, hdep1, hval1⟩ :=
        ih r (by omega) u' v' gs hgs
      set gs1 := gs ++ ex1
      obtain ⟨ex2, w2, hgood2, hw2lt, hcnt2, hdep2, hval2⟩ :=
        buildRankPair gs1 hgood1 (u ⟨r, by omega⟩) (u ⟨r + 1, by omega⟩)
          (v ⟨r, by omega⟩) (v ⟨r + 1, by omega⟩)
      set gs2 := gs1 ++ ex2
      have hw1lt2 : w1 < n + m + gs2.length := by simp only [gs2, List.length_append]; omega
      obtain ⟨ex3, w3, hgood3, hw3lt, hcnt3, hdep3, hval3⟩ := buildXor gs2 hgood2 w1 w2 hw1lt2 hw2lt
      refine ⟨ex1 ++ ex2 ++ ex3, w3, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [gs2, gs1, List.append_assoc] using hgood3
      · simpa [gs2, gs1, List.append_assoc] using hw3lt
      · have hEq : gs ++ (ex1 ++ ex2 ++ ex3) = gs2 ++ ex3 := by
          simp [gs2, gs1, List.append_assoc]
        rw [hEq, hcnt3, hcnt2]
        omega
      · have hEq : gs ++ (ex1 ++ ex2 ++ ex3) = gs2 ++ ex3 := by
          simp [gs2, gs1, List.append_assoc]
        rw [hEq, hdep3, depOf_append_prefix n m gs1 ex2 w1 hw1lt]
        exact max_le hdep1 hdep2
      · intro a b
        have hEq : gs ++ (ex1 ++ ex2 ++ ex3) = gs2 ++ ex3 := by
          simp [gs2, gs1, List.append_assoc]
        rw [hEq, hval3 a b, valOf_append_prefix gs1 ex2 w1 hw1lt a b, hval1 a b, hval2 a b]
        have hsum : ∑ i : Fin r, u' i a * v' i b =
            ∑ i : Fin r, u i.castSucc.castSucc a * v i.castSucc.castSucc b :=
          Finset.sum_congr rfl fun i _ => rfl
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, ← hsum]
        have hlast1 : (Fin.last r).castSucc = (⟨r, by omega⟩ : Fin (r + 2)) := rfl
        have hlast2 : Fin.last (r + 1) = (⟨r + 1, by omega⟩ : Fin (r + 2)) := rfl
        rw [hlast1, hlast2]
        ring

private theorem buildManyRank {n m q r : ℕ} (G : Fin q → Fin n → Fin m → Bool)
    (hG : ∀ j : Fin q, ∃ (u : Fin r → Fin n → ZMod 2) (v : Fin r → Fin m → ZMod 2),
      ∀ a b, b2z (G j a b) = ∑ i : Fin r, u i a * v i b) :
    ∀ (js : List (Fin q)) (gs : List Gate), GoodCirc n m gs →
      ∃ (extra : List Gate) (taps : Fin q → ℕ),
        let gs' := gs ++ extra
        GoodCirc n m gs' ∧
        gs'.countP nonlinear ≤ gs.countP nonlinear + js.length * ((r + 1) / 2) ∧
        ∀ j ∈ js, taps j < n + m + gs'.length ∧ depOf n m gs' (taps j) ≤ 1 ∧
          ∀ a b, valOf gs' (taps j) a b = b2z (G j a b) := by
  intro js
  induction js with
  | nil =>
    intro gs hgs
    exact ⟨[], fun _ => 0, by simpa using hgs, by simp, fun _ h => by simp at h⟩
  | cons j0 rest ih =>
    intro gs hgs
    obtain ⟨u, v, huv⟩ := hG j0
    obtain ⟨ex1, w1, hgood1, hw1lt, hcnt1, hdep1, hval1⟩ := buildRankSum r u v gs hgs
    set gs1 := gs ++ ex1
    obtain ⟨ex2, taps2, hgood2, hcnt2, htaps2⟩ := ih gs1 hgood1
    let taps : Fin q → ℕ := fun j => if j = j0 then w1 else taps2 j
    refine ⟨ex1 ++ ex2, taps, ?_, ?_, ?_⟩
    · simpa [gs1, List.append_assoc] using hgood2
    · have hEq : gs ++ (ex1 ++ ex2) = gs1 ++ ex2 := by simp [gs1, List.append_assoc]
      rw [hEq]
      simp only [List.length_cons]
      have : (rest.length + 1) * ((r + 1) / 2) = rest.length * ((r + 1) / 2) + (r + 1) / 2 := by ring
      omega
    · intro j hj
      have hEq : gs ++ (ex1 ++ ex2) = gs1 ++ ex2 := by simp [gs1, List.append_assoc]
      rw [hEq]
      by_cases hjj0 : j = j0
      · subst hjj0
        simp only [taps, ↓reduceIte]
        refine ⟨by simp only [List.length_append]; omega,
          by rw [depOf_append_prefix n m gs1 ex2 w1 hw1lt]; exact hdep1, fun a b => ?_⟩
        rw [valOf_append_prefix gs1 ex2 w1 hw1lt a b, hval1 a b, huv a b]
      · simp only [taps, hjj0, ↓reduceIte]
        have hmem : j ∈ rest := by
          rcases List.mem_cons.1 hj with rfl | h
          · exact False.elim (hjj0 rfl)
          · exact h
        exact htaps2 j hmem

private theorem fits_of_rank_le {n m q r : ℕ} (G : Fin q → Fin n → Fin m → Bool)
    (hG : ∀ j : Fin q, ∃ (u : Fin r → Fin n → ZMod 2) (v : Fin r → Fin m → ZMod 2),
      ∀ a b, b2z (G j a b) = ∑ i : Fin r, u i a * v i b) :
    fits n m q G (q * ((r + 1) / 2)) := by
  have hnil : GoodCirc n m [] := ⟨fun j hj => by simp at hj, fun g hg => by simp at hg⟩
  obtain ⟨gs, taps, hgood, hcnt, htaps⟩ := buildManyRank G hG (List.finRange q) [] hnil
  simp only [List.nil_append, List.countP_nil, zero_add, List.length_finRange] at hgood hcnt htaps
  refine ⟨⟨gs, 0⟩, taps, hgood.1, hgood.2, hcnt, fun j => ?_⟩
  obtain ⟨_, hdep, hval⟩ := htaps j (List.mem_finRange j)
  refine ⟨hdep, fun a b => ?_⟩
  apply b2z_inj
  exact hval a b

private def qBinom (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | g + 1, 0 => 1
  | g + 1, r + 1 => q ^ (r + 1) * qBinom q g (r + 1) + qBinom q g r

private def qFact (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => qFact q r * (q ^ (r + 1) - 1)

private theorem qBinom_eq_zero_of_lt (q : ℕ) : ∀ n k : ℕ, n < k → qBinom q n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k => simp [qBinom, ih (k + 1) (by omega), ih k (by omega)]

private theorem qFact_mul_qBinom_eq (q : ℕ) (hq : 1 ≤ q) :
    ∀ g r : ℕ, r ≤ g → qFact q r * qBinom q g r = ∏ i ∈ Finset.range r, (q ^ (g - i) - 1) := by
  intro g
  induction g with
  | zero =>
    intro r hr
    have hr0 : r = 0 := by omega
    subst hr0
    simp [qFact, qBinom]
  | succ g ih =>
    intro r hr
    cases r with
    | zero => simp [qFact, qBinom]
    | succ r =>
      by_cases hrg : r + 1 ≤ g
      · simp only [qBinom, mul_add]
        have s1 : qFact q (r + 1) * (q ^ (r + 1) * qBinom q g (r + 1)) =
            q ^ (r + 1) * (qFact q (r + 1) * qBinom q g (r + 1)) := by ring
        have s2 : qFact q (r + 1) * qBinom q g r =
            (q ^ (r + 1) - 1) * (qFact q r * qBinom q g r) := by
          simp only [qFact]; ring
        rw [s1, s2, ih (r + 1) hrg, ih r (by omega)]
        rw [Finset.prod_range_succ, Finset.prod_range_succ']
        have hshift : ∏ i ∈ Finset.range r, (q ^ (g + 1 - (i + 1)) - 1) =
            ∏ i ∈ Finset.range r, (q ^ (g - i) - 1) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          simp
        rw [hshift]
        simp only [Nat.sub_zero]
        have hle1 : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ hq
        have hle2 : 1 ≤ q ^ (g - r) := Nat.one_le_pow _ _ hq
        have hle3 : 1 ≤ q ^ (g + 1) := Nat.one_le_pow _ _ hq
        have hpow_mul : q ^ (r + 1) * q ^ (g - r) = q ^ (g + 1) := by
          rw [← pow_add]; congr 1; omega
        have hfactor : q ^ (r + 1) * (q ^ (g - r) - 1) + (q ^ (r + 1) - 1) = q ^ (g + 1) - 1 := by
          zify [hle1, hle2, hle3]
          have hz : ((q ^ (r + 1) : ℕ) : ℤ) * ((q ^ (g - r) : ℕ) : ℤ) = ((q ^ (g + 1) : ℕ) : ℤ) := by
            exact_mod_cast hpow_mul
          linarith
        set P := ∏ i ∈ Finset.range r, (q ^ (g - i) - 1)
        calc q ^ (r + 1) * (P * (q ^ (g - r) - 1)) + (q ^ (r + 1) - 1) * P
            = P * (q ^ (r + 1) * (q ^ (g - r) - 1) + (q ^ (r + 1) - 1)) := by ring
          _ = P * (q ^ (g + 1) - 1) := by rw [hfactor]
      · have hreq : r = g := by omega
        subst hreq
        simp only [qBinom, qBinom_eq_zero_of_lt q r (r + 1) (by omega), mul_zero, zero_add]
        have s2 : qFact q (r + 1) * qBinom q r r =
            (q ^ (r + 1) - 1) * (qFact q r * qBinom q r r) := by
          simp only [qFact]; ring
        rw [s2, ih r (le_refl _), Finset.prod_range_succ']
        simp only [Nat.sub_zero]
        rw [mul_comm]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        simp

private theorem qFact_mul_qBinom_le (q : ℕ) (hq : 1 ≤ q) (g r : ℕ) (hr : r ≤ g) :
    qFact q r * qBinom q g r ≤ q ^ (r * g - r * (r - 1) / 2) := by
  rw [qFact_mul_qBinom_eq q hq g r hr]
  calc ∏ i ∈ Finset.range r, (q ^ (g - i) - 1)
      ≤ ∏ i ∈ Finset.range r, q ^ (g - i) := Finset.prod_le_prod' fun i _ => Nat.sub_le _ _
    _ = q ^ (∑ i ∈ Finset.range r, (g - i)) := by rw [Finset.prod_pow_eq_pow_sum]
    _ = q ^ (r * g - r * (r - 1) / 2) := by
        congr 1
        have hsum : ∑ i ∈ Finset.range r, (g - i) + ∑ i ∈ Finset.range r, i = r * g := by
          rw [← Finset.sum_add_distrib]
          have : ∀ i ∈ Finset.range r, g - i + i = g := fun i hi => by
            rw [Finset.mem_range] at hi; omega
          rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]
        have htri : ∑ i ∈ Finset.range r, i = r * (r - 1) / 2 := Finset.sum_range_id r
        omega

private theorem qFact_lower (q : ℕ) (hq : 4 ≤ q) :
    ∀ r : ℕ, ((q - 2) * q ^ r + 1) * q ^ (r * (r + 1) / 2) ≤ (q - 1) * qFact q r * q ^ r := by
  intro r
  induction r with
  | zero =>
    simp only [pow_zero, mul_one, zero_mul, Nat.zero_div, qFact]
    omega
  | succ r ih =>
    have hq1 : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ (by omega)
    have hstep : (q - 1) * qFact q (r + 1) * q ^ (r + 1) =
        ((q - 1) * qFact q r * q ^ r) * (q * (q ^ (r + 1) - 1)) := by
      simp only [qFact, pow_succ]
      ring
    rw [hstep]
    have hmul : (((q - 2) * q ^ r + 1) * q ^ (r * (r + 1) / 2)) * (q * (q ^ (r + 1) - 1)) ≤
        ((q - 1) * qFact q r * q ^ r) * (q * (q ^ (r + 1) - 1)) :=
      Nat.mul_le_mul_right _ ih
    refine le_trans ?_ hmul
    have htri : (r + 1) * (r + 2) / 2 = r * (r + 1) / 2 + (r + 1) := by
      have : (r + 1) * (r + 2) = r * (r + 1) + 2 * (r + 1) := by ring
      omega
    rw [htri, pow_add q (r * (r + 1) / 2) (r + 1)]
    have hrearr1 : ((q - 2) * q ^ (r + 1) + 1) * (q ^ (r * (r + 1) / 2) * q ^ (r + 1)) =
        q ^ (r * (r + 1) / 2) * (((q - 2) * q ^ (r + 1) + 1) * q ^ (r + 1)) := by ring
    have hrearr2 : ((q - 2) * q ^ r + 1) * q ^ (r * (r + 1) / 2) * (q * (q ^ (r + 1) - 1)) =
        q ^ (r * (r + 1) / 2) * (((q - 2) * q ^ (r + 1) + q) * (q ^ (r + 1) - 1)) := by
      rw [pow_succ]; ring
    rw [hrearr1, hrearr2]
    apply Nat.mul_le_mul_left
    have hqp : q ≤ q ^ (r + 1) := by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    zify [hq1, (by omega : 2 ≤ q)]
    nlinarith

private theorem even_mul_pred (r : ℕ) : 2 * (r * (r - 1) / 2) = r * (r - 1) := by
  cases r with
  | zero => simp
  | succ r' =>
    have h2 : 2 ∣ (r' + 1) * r' := by
      rcases Nat.even_or_odd r' with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨(k + k + 1) * k, by ring⟩
      · exact ⟨(k + 1) * (2 * k + 1), by ring⟩
    simpa using Nat.mul_div_cancel' h2

private theorem even_mul_succ (r : ℕ) : 2 * (r * (r + 1) / 2) = r * (r + 1) := by
  have h := even_mul_pred (r + 1)
  simpa [mul_comm] using h

private theorem even_mul_3pred (r : ℕ) : 2 * (r * (3 * r - 1) / 2) = r * (3 * r - 1) := by
  cases r with
  | zero => simp
  | succ r' =>
    have h2 : 2 ∣ (r' + 1) * (3 * (r' + 1) - 1) := by
      rcases Nat.even_or_odd r' with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · refine ⟨(k + k + 1) * (3 * k + 1), ?_⟩
        have : 3 * (k + k + 1) - 1 = 6 * k + 2 := by omega
        rw [this]; ring
      · refine ⟨(k + 1) * (6 * k + 5), ?_⟩
        have : 3 * (2 * k + 1 + 1) - 1 = 6 * k + 5 := by omega
        rw [this]; ring
    exact Nat.mul_div_cancel' h2

private theorem two_mul_qBinom_le (q : ℕ) (hq : 4 ≤ q) (g r : ℕ) (hr : r ≤ g) :
    2 * qBinom q g r ≤ 3 * q ^ (r * (g - r)) := by
  have h1 := qFact_mul_qBinom_le q (by omega) g r hr
  have h2 := qFact_lower q hq r
  have h3 : 2 * q ^ (r * (r + 1) / 2) ≤ 3 * qFact q r := by
    have hqr_pos : 0 < q ^ r := Nat.pow_pos (by omega)
    have h4 : 2 * (q - 1) * q ^ r ≤ 3 * ((q - 2) * q ^ r + 1) := by
      have : 2 * (q - 1) ≤ 3 * (q - 2) := by omega
      nlinarith
    have h5 : 2 * (q - 1) * q ^ r * q ^ (r * (r + 1) / 2) ≤
        3 * (((q - 2) * q ^ r + 1) * q ^ (r * (r + 1) / 2)) := by
      have := Nat.mul_le_mul_right (q ^ (r * (r + 1) / 2)) h4
      linarith
    have h6 : 2 * (q - 1) * q ^ r * q ^ (r * (r + 1) / 2) ≤
        3 * ((q - 1) * qFact q r * q ^ r) :=
      h5.trans (Nat.mul_le_mul_left 3 h2)
    have h7 : ((q - 1) * q ^ r) * (2 * q ^ (r * (r + 1) / 2)) ≤
        ((q - 1) * q ^ r) * (3 * qFact q r) := by linarith
    exact Nat.le_of_mul_le_mul_left h7 (Nat.mul_pos (by omega) hqr_pos)
  have hexp : r * (g - r) + r * (r + 1) / 2 = r * g - r * (r - 1) / 2 := by
    cases r with
    | zero => simp
    | succ r' =>
      have he1 := even_mul_succ (r' + 1)
      have he2 := even_mul_pred (r' + 1)
      have hsub : (r' + 1) * (g - (r' + 1)) = (r' + 1) * g - (r' + 1) * (r' + 1) := Nat.mul_sub _ _ _
      have hle1 : (r' + 1) * (r' + 1) ≤ (r' + 1) * g := Nat.mul_le_mul_left (r' + 1) hr
      have htri : (r' + 1) * (r' + 1 + 1) + (r' + 1) * r' = 2 * ((r' + 1) * (r' + 1)) := by ring
      simp only [Nat.add_sub_cancel] at he2 ⊢
      omega
  have hpos : 0 < q ^ (r * (r + 1) / 2) := Nat.pow_pos (by omega)
  have hmul : q ^ (r * (r + 1) / 2) * (2 * qBinom q g r) ≤
      q ^ (r * (r + 1) / 2) * (3 * q ^ (r * (g - r))) := by
    calc q ^ (r * (r + 1) / 2) * (2 * qBinom q g r)
        = (2 * q ^ (r * (r + 1) / 2)) * qBinom q g r := by ring
      _ ≤ (3 * qFact q r) * qBinom q g r := Nat.mul_le_mul_right _ h3
      _ = 3 * (qFact q r * qBinom q g r) := by ring
      _ ≤ 3 * q ^ (r * g - r * (r - 1) / 2) := Nat.mul_le_mul_left 3 h1
      _ = 3 * q ^ (r * (g - r) + r * (r + 1) / 2) := by rw [hexp]
      _ = q ^ (r * (r + 1) / 2) * (3 * q ^ (r * (g - r))) := by rw [pow_add]; ring
  exact Nat.le_of_mul_le_mul_left hmul hpos

private theorem delta_step (d g r : ℕ) (hrg : r + 1 ≤ g) (hrd : 2 * (r + 1) ≤ d) :
    (r * (d + g) - r * (3 * r - 1) / 2) + 2 ≤
      (r + 1) * (d + g) - (r + 1) * (3 * (r + 1) - 1) / 2 := by
  have he1 := even_mul_3pred r
  have he2 := even_mul_3pred (r + 1)
  have hle1 : r * (3 * r - 1) ≤ 2 * (r * (d + g)) := by
    cases r with
    | zero => simp
    | succ r' =>
      have : 3 * (r' + 1) - 1 = 3 * r' + 2 := by omega
      rw [this]; nlinarith
  have hle2 : (r + 1) * (3 * (r + 1) - 1) ≤ 2 * ((r + 1) * (d + g)) := by
    have : 3 * (r + 1) - 1 = 3 * r + 2 := by omega
    rw [this]; nlinarith
  have hdiff : (r + 1) * (3 * (r + 1) - 1) = r * (3 * r - 1) + 2 * (3 * r + 1) := by
    cases r with
    | zero => simp
    | succ r' =>
      have h1 : 3 * (r' + 1 + 1) - 1 = 3 * r' + 5 := by omega
      have h2 : 3 * (r' + 1) - 1 = 3 * r' + 2 := by omega
      rw [h1, h2]; ring
  have hmul : (r + 1) * (d + g) = r * (d + g) + (d + g) := by ring
  omega

private theorem delta_top (m g dimR : ℕ) (hm : 0 < m) (hmg : m ≤ g * (g + 1) / 2)
    (hdimR : dimR ≤ 1) (hdimRm : dimR + 1 ≤ m) :
    let d := m - 1 - dimR
    let rmax := min g (d / 2)
    rmax * (d + g) - rmax * (3 * rmax - 1) / 2 + m ≤ (d + 1) * g := by
  intro d rmax
  have hmd : m = d + 1 + dimR := by omega
  by_cases hgd : g ≤ d / 2
  · have hrmax : rmax = g := min_eq_left hgd
    rw [hrmax]
    have he1 := even_mul_3pred g
    have he2 := even_mul_succ g
    have h2g : 2 * g ≤ d := by omega
    have hle : g * (3 * g - 1) ≤ 2 * (g * (d + g)) := by
      cases g with
      | zero => simp
      | succ g' =>
        have : 3 * (g' + 1) - 1 = 3 * g' + 2 := by omega
        rw [this]; nlinarith
    have htri : g * (3 * g - 1) + g * (g + 1) = 4 * (g * g) := by
      cases g with
      | zero => simp
      | succ g' =>
        have : 3 * (g' + 1) - 1 = 3 * g' + 2 := by omega
        rw [this]; ring
    have hmul1 : g * (d + g) = g * d + g * g := by ring
    have hmul2 : (d + 1) * g = g * d + g := by ring
    have hgg : g * (g + 1) = g * g + g := by ring
    omega
  · have hrmax : rmax = d / 2 := min_eq_right (by omega)
    rw [hrmax]
    have hd_mod : d = 2 * (d / 2) + d % 2 := (Nat.div_add_mod d 2).symm
    have hmod_le : d % 2 ≤ 1 := by omega
    have hsg : d / 2 + 1 ≤ g := by omega
    match hdeq : d / 2 with
    | 0 =>
      simp only [zero_mul, Nat.zero_sub, zero_add]
      have hd_le : d ≤ 1 := by omega
      have hg1 : 1 ≤ g := by omega
      by_cases hm1 : m = 1
      · nlinarith
      · have hg2 : 2 ≤ g := by
          by_contra hlt
          have hg1' : g = 1 := by omega
          rw [hg1'] at hmg
          omega
        nlinarith
    | 1 =>
      show 1 * (d + g) - 1 * (3 * 1 - 1) / 2 + m ≤ (d + 1) * g
      have h1 : 1 * (3 * 1 - 1) / 2 = 1 := by decide
      rw [h1, one_mul]
      have hd_ge : 2 ≤ d := by omega
      have hd_le : d ≤ 3 := by omega
      have hg2 : 2 ≤ g := by omega
      by_cases hm3 : m ≤ 3
      · have : d + g - 1 + m ≤ d + g + 2 := by omega
        nlinarith
      · have hg3 : 3 ≤ g := by
          by_contra hlt
          have hg2' : g = 2 := by omega
          rw [hg2'] at hmg
          omega
        have : d + g - 1 + m ≤ d + g + 4 := by omega
        nlinarith
    | s'' + 2 =>
      set s := s'' + 2
      have hs_def : s = s'' + 2 := rfl
      have hsg' : s + 1 ≤ g := by omega
      have hd_eq : d = 2 * s + d % 2 := by omega
      have he := even_mul_3pred s
      have h3s : 3 * s - 1 = 3 * s'' + 5 := by omega
      have hle : s * (3 * s - 1) ≤ 2 * (s * (d + g)) := by
        rw [h3s]
        have h1 : 3 * s'' + 5 ≤ 2 * (d + g) := by omega
        calc s * (3 * s'' + 5) ≤ s * (2 * (d + g)) := Nat.mul_le_mul_left s h1
          _ = 2 * (s * (d + g)) := by ring
      have hgoal2 : 2 * (s * (d + g)) + 2 * m ≤ 2 * ((d + 1) * g) + s * (3 * s - 1) := by
        rw [h3s, hmd, hd_eq]
        have hg_mul : (s + d % 2 + 1) * (s + 1) ≤ (s + d % 2 + 1) * g :=
          Nat.mul_le_mul_left _ hsg'
        have hs_sq : s + 2 ≤ s * s := by nlinarith [hs_def]
        nlinarith [hs_def, hg_mul, hs_sq, hdimR, hmod_le]
      omega

private theorem geom_sum_bound (q : ℕ) (hq : 4 ≤ q) :
    ∀ k M : ℕ, ∀ f : ℕ → ℕ,
      (∀ i < k, f i + 2 ≤ f (i + 1)) → f k ≤ M →
      15 * (∑ i ∈ Finset.range (k + 1), q ^ (f i)) ≤ 16 * q ^ M := by
  intro k
  induction k with
  | zero =>
    intro M f _ hfk
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    have hpow : q ^ f 0 ≤ q ^ M := Nat.pow_le_pow_right (by omega) hfk
    omega
  | succ k ih =>
    intro M f hstep hfk
    rw [Finset.sum_range_succ]
    have hstepk := hstep k (by omega)
    have hfk' : f k ≤ M - 2 := by omega
    have hih := ih (M - 2) f (fun i hi => hstep i (by omega)) hfk'
    have h2le : 2 ≤ M := by omega
    have hq2 : 16 * q ^ (M - 2) ≤ q ^ M := by
      have hpow : q ^ M = q ^ (M - 2) * q ^ 2 := by
        rw [← pow_add]; congr 1; omega
      rw [hpow]
      have h16 : 16 ≤ q ^ 2 := by nlinarith
      calc 16 * q ^ (M - 2) ≤ q ^ 2 * q ^ (M - 2) := Nat.mul_le_mul_right _ h16
        _ = q ^ (M - 2) * q ^ 2 := mul_comm _ _
    have hlast : q ^ f (k + 1) ≤ q ^ M := Nat.pow_le_pow_right (by omega) hfk
    have hprev : 15 * (∑ i ∈ Finset.range (k + 1), q ^ f i) ≤ q ^ M := hih.trans hq2
    omega

private theorem union_bound_arith (q m g dimR : ℕ) (hq : 4 ≤ q) (hm : 0 < m)
    (hmg : m ≤ g * (g + 1) / 2) (hdimR : dimR ≤ 1) (hdimRm : dimR + 1 ≤ m) :
    let d := m - 1 - dimR
    let rmax := min g (d / 2)
    (q ^ m - 1) * q ^ (g * dimR) *
      (∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2)) <
      (q - 1) * q ^ (m * g) := by
  intro d rmax
  let E : ℕ → ℕ := fun r => r * (d + g) - r * (3 * r - 1) / 2
  have hterm : ∀ r ∈ Finset.range (rmax + 1),
      2 * (qBinom q g r * q ^ (r * d - r * (r - 1) / 2)) ≤ 3 * q ^ (E r) := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hrg : r ≤ g := by omega
    have hrd : 2 * r ≤ d := by omega
    have hqb := two_mul_qBinom_le q hq g r hrg
    have hexp : r * (g - r) + (r * d - r * (r - 1) / 2) = E r := by
      dsimp only [E]
      have hsub : r * (g - r) = r * g - r * r := Nat.mul_sub _ _ _
      have hle1 : r * r ≤ r * g := Nat.mul_le_mul_left r hrg
      have he1 := even_mul_pred r
      have he2 := even_mul_3pred r
      have hle2 : r * (r - 1) ≤ 2 * (r * d) := by
        cases r with
        | zero => simp
        | succ r' => simp only [Nat.add_sub_cancel]; nlinarith
      have h3r : r * (3 * r - 1) = 2 * (r * r) + r * (r - 1) := by
        cases r with
        | zero => simp
        | succ r' =>
          have : 3 * (r' + 1) - 1 = 3 * r' + 2 := by omega
          rw [this]; simp; ring
      have hmul : r * (d + g) = r * d + r * g := by ring
      omega
    calc 2 * (qBinom q g r * q ^ (r * d - r * (r - 1) / 2))
        = (2 * qBinom q g r) * q ^ (r * d - r * (r - 1) / 2) := by ring
      _ ≤ (3 * q ^ (r * (g - r))) * q ^ (r * d - r * (r - 1) / 2) := Nat.mul_le_mul_right _ hqb
      _ = 3 * q ^ (r * (g - r) + (r * d - r * (r - 1) / 2)) := by rw [mul_assoc, ← pow_add]
      _ = 3 * q ^ (E r) := by rw [hexp]
  have hsum2 : 2 * (∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2)) ≤
      3 * (∑ r ∈ Finset.range (rmax + 1), q ^ (E r)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have htop : E rmax + m ≤ (d + 1) * g := delta_top m g dimR hm hmg hdimR hdimRm
  have hM : E rmax ≤ (d + 1) * g - m := by omega
  have hgeom := geom_sum_bound q hq rmax ((d + 1) * g - m) E
    (fun i hi => delta_step d g i (by omega) (by omega)) hM
  have hS : 10 * (∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2)) ≤
      16 * q ^ ((d + 1) * g - m) := by
    have h1 : 30 * (∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2)) ≤
        48 * q ^ ((d + 1) * g - m) := by
      calc 30 * (∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2))
          = 15 * (2 * (∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2))) := by ring
        _ ≤ 15 * (3 * (∑ r ∈ Finset.range (rmax + 1), q ^ (E r))) := Nat.mul_le_mul_left 15 hsum2
        _ = 3 * (15 * (∑ r ∈ Finset.range (rmax + 1), q ^ (E r))) := by ring
        _ ≤ 3 * (16 * q ^ ((d + 1) * g - m)) := Nat.mul_le_mul_left 3 hgeom
        _ = 48 * q ^ ((d + 1) * g - m) := by ring
    omega
  have hle_mg : m ≤ (d + 1) * g := by omega
  have hpow_comb : q ^ m * q ^ (g * dimR) * q ^ ((d + 1) * g - m) = q ^ (m * g) := by
    rw [← pow_add, ← pow_add]
    congr 1
    have hmd : m = d + 1 + dimR := by omega
    have : m * g = g * dimR + (d + 1) * g := by
      rw [hmd]; ring
    omega
  have hpos : 0 < q ^ (m * g) := Nat.pow_pos (by omega)
  have h10 : 10 * ((q ^ m - 1) * q ^ (g * dimR) *
      (∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2))) ≤
      16 * q ^ (m * g) := by
    calc 10 * ((q ^ m - 1) * q ^ (g * dimR) *
            (∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2)))
        = (q ^ m - 1) * q ^ (g * dimR) *
            (10 * (∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2))) := by ring
      _ ≤ q ^ m * q ^ (g * dimR) * (16 * q ^ ((d + 1) * g - m)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) hS
      _ = 16 * (q ^ m * q ^ (g * dimR) * q ^ ((d + 1) * g - m)) := by ring
      _ = 16 * q ^ (m * g) := by rw [hpow_comb]
  have h30 : 16 * q ^ (m * g) < 10 * ((q - 1) * q ^ (m * g)) := by
    have : 16 < 10 * (q - 1) := by omega
    nlinarith
  omega

private theorem card_submodule_eq_pow {E K : Type} [Field E] [Fintype E] [Field K] [Algebra E K]
    [FiniteDimensional E K] (U : Submodule E K) [Fintype U] :
    Fintype.card U = (Fintype.card E) ^ (Module.finrank E U) := by
  exact Module.card_eq_pow_finrank (K := E) (V := U)

private def perpSub {E K : Type} [Field E] [Field K] [Algebra E K]
    (φ : K →ₗ[E] E) (U : Submodule E K) : Submodule E K :=
  { carrier := { y : K | ∀ x ∈ U, φ (x * y) = 0 }, add_mem' := fun ha hb x hx => by
      rw [mul_add, map_add, ha x hx, hb x hx, add_zero]
    zero_mem' := fun x _ => by simp
    smul_mem' := fun c y hy x hx => by
      have : x * (c • y) = c • (x * y) := by rw [mul_smul_comm]
      rw [this, map_smul, hy x hx, smul_zero] }

private theorem finrank_perpSub {E K : Type} [Field E] [Field K] [Algebra E K]
    [FiniteDimensional E K] (φ : K →ₗ[E] E) (hφ : φ ≠ 0) (U : Submodule E K) :
    Module.finrank E U + Module.finrank E (perpSub φ U) = Module.finrank E K := by
  let Φ : K →ₗ[E] (K →ₗ[E] E) :=
    { toFun := fun y =>
        { toFun := fun x => φ (x * y)
          map_add' := fun x1 x2 => by rw [add_mul, map_add]
          map_smul' := fun c x => by rw [smul_mul_assoc, map_smul, RingHom.id_apply] }
      map_add' := fun y1 y2 => by ext x; simp [mul_add, map_add]
      map_smul' := fun c y => by ext x; simp [mul_smul_comm, map_smul] }
  have hΦ_inj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hy0
    have hex : ∃ a : K, φ a ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hφ (LinearMap.ext hall)
    obtain ⟨a, ha⟩ := hex
    have h0 : Φ y (a * y⁻¹) = 0 := by rw [hy]; rfl
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc, inv_mul_cancel₀ hy0, mul_one] at h0
    exact ha h0
  have hΦ_surj : Function.Surjective Φ := by
    have hfr : Module.finrank E K = Module.finrank E (K →ₗ[E] E) := by
      rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hΦ_inj
  let res : (K →ₗ[E] E) →ₗ[E] (U →ₗ[E] E) :=
    { toFun := fun f => f.comp U.subtype
      map_add' := fun f1 f2 => by ext x; rfl
      map_smul' := fun c f => by ext x; rfl }
  have hres_surj : Function.Surjective res := by
    intro g
    obtain ⟨V, hV⟩ := Submodule.exists_isCompl U
    let e := Submodule.prodEquivOfIsCompl U V hV
    let f : K →ₗ[E] E := g.comp (LinearMap.fst E U V |>.comp e.symm.toLinearMap)
    refine ⟨f, ?_⟩
    ext ⟨u, hu⟩
    have he : e (⟨u, hu⟩, (0 : V)) = u := by simp [e]
    have hsymm : e.symm u = (⟨u, hu⟩, (0 : V)) := e.symm_apply_eq.2 he.symm
    simp [res, f, hsymm]
  let comp : K →ₗ[E] (U →ₗ[E] E) := res.comp Φ
  have hcomp_surj : Function.Surjective comp := hres_surj.comp hΦ_surj
  have hker : LinearMap.ker comp = perpSub φ U := by
    ext y
    simp only [LinearMap.mem_ker, comp, res, Φ, LinearMap.comp_apply, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.ext_iff, LinearMap.zero_apply, Subtype.forall, Submodule.coe_subtype]
    rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker comp
  rw [LinearMap.range_eq_top.2 hcomp_surj, finrank_top, hker, Module.finrank_linearMap,
    Module.finrank_self, mul_one] at hrn
  exact hrn

private theorem finrank_inter_perpSub_of_nondeg {E K : Type} [Field E] [Field K] [Algebra E K]
    [FiniteDimensional E K] (φ : K →ₗ[E] E) (W U : Submodule E K)
    (hnondeg : W ⊓ perpSub φ W = ⊥) (hUW : U ≤ W) :
    Module.finrank E U + Module.finrank E (W ⊓ perpSub φ U : Submodule E K) = Module.finrank E W := by
  let ΦW : W →ₗ[E] (W →ₗ[E] E) :=
    { toFun := fun y =>
        { toFun := fun x => φ (x.1 * y.1)
          map_add' := fun x1 x2 => by simp [add_mul, map_add]
          map_smul' := fun c x => by simp [smul_mul_assoc, map_smul] }
      map_add' := fun y1 y2 => by ext x; simp [mul_add, map_add]
      map_smul' := fun c y => by ext x; simp [mul_smul_comm, map_smul] }
  have hΦW_inj : Function.Injective ΦW := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hyperp : y.1 ∈ perpSub φ W := by
      intro x hx
      have h0 : ΦW y ⟨x, hx⟩ = 0 := by rw [hy]; rfl
      exact h0
    have hmem : y.1 ∈ W ⊓ perpSub φ W := ⟨y.2, hyperp⟩
    rw [hnondeg, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  have hΦW_surj : Function.Surjective ΦW := by
    have hfr : Module.finrank E W = Module.finrank E (W →ₗ[E] E) := by
      rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hΦW_inj
  let U' : Submodule E W := U.comap W.subtype
  have hU'_fr : Module.finrank E U' = Module.finrank E U := by
    have heq : U'.map W.subtype = U := Submodule.map_comap_eq_of_le (by simpa using hUW)
    have hrange : LinearMap.range (W.subtype.comp U'.subtype) = U'.map W.subtype := by
      ext x; simp [Submodule.mem_map]
    rw [← heq, ← hrange]
    exact (LinearMap.finrank_range_of_inj (Subtype.val_injective.comp Subtype.val_injective)).symm
  let res : (W →ₗ[E] E) →ₗ[E] (U' →ₗ[E] E) :=
    { toFun := fun f => f.comp U'.subtype
      map_add' := fun f1 f2 => by ext x; rfl
      map_smul' := fun c f => by ext x; rfl }
  have hres_surj : Function.Surjective res := by
    intro g
    obtain ⟨V, hV⟩ := Submodule.exists_isCompl U'
    let e := Submodule.prodEquivOfIsCompl U' V hV
    let f : W →ₗ[E] E := g.comp (LinearMap.fst E U' V |>.comp e.symm.toLinearMap)
    refine ⟨f, ?_⟩
    ext ⟨u, hu⟩
    have he : e (⟨u, hu⟩, (0 : V)) = u := by simp [e]
    have hsymm : e.symm u = (⟨u, hu⟩, (0 : V)) := e.symm_apply_eq.2 he.symm
    simp [res, f, hsymm]
  let comp : W →ₗ[E] (U' →ₗ[E] E) := res.comp ΦW
  have hcomp_surj : Function.Surjective comp := hres_surj.comp hΦW_surj
  have hker_map : (LinearMap.ker comp).map W.subtype = W ⊓ perpSub φ U := by
    ext y
    constructor
    · rintro ⟨⟨w, hw⟩, hcomp, rfl⟩
      refine ⟨hw, fun x hx => ?_⟩
      have h0 : comp ⟨w, hw⟩ ⟨⟨x, hUW hx⟩, hx⟩ = 0 := by
        rw [LinearMap.mem_ker.1 hcomp]; rfl
      exact h0
    · rintro ⟨hw, hp⟩
      refine ⟨⟨y, hw⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      ext ⟨⟨x, hxW⟩, hxU⟩
      exact hp x hxU
  have hker_fr : Module.finrank E (LinearMap.ker comp) = Module.finrank E (W ⊓ perpSub φ U : Submodule E K) := by
    have hrange : LinearMap.range (W.subtype.comp (LinearMap.ker comp).subtype) = (LinearMap.ker comp).map W.subtype := by
      ext x; simp [Submodule.mem_map]
    rw [← hker_map, ← hrange]
    exact (LinearMap.finrank_range_of_inj (Subtype.val_injective.comp Subtype.val_injective)).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker comp
  have hlin : Module.finrank E (U' →ₗ[E] E) = Module.finrank E U' := by
    haveI : Module.Free E U' := Module.Free.of_divisionRing E U'
    rw [Module.finrank_linearMap E E U' E, Module.finrank_self, mul_one]
  rw [LinearMap.range_eq_top.2 hcomp_surj, finrank_top, hlin, hU'_fr, hker_fr] at hrn
  exact hrn

private theorem card_iso_tuples_nondeg {E K : Type} [Field E] [Fintype E] [Field K] [Algebra E K]
    [FiniteDimensional E K] [Fintype K] (φ : K →ₗ[E] E) (W : Submodule E K)
    (hnondeg : W ⊓ perpSub φ W = ⊥) :
    let d := Module.finrank E W
    let q := Fintype.card E
    ∀ g r : ℕ,
      (Finset.univ.filter (fun w : Fin g → W =>
        (∀ i j, φ ((w i : K) * (w j : K)) = 0) ∧
        Module.finrank E (Submodule.span E (Set.range fun i => (w i : K))) = r)).card ≤
      if 2 * r ≤ d then qBinom q g r * q ^ (r * d - r * (r - 1) / 2) else 0 := by
  classical
  intro d q g
  induction g with
  | zero =>
    intro r
    cases r with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_le, ↓reduceIte, qBinom, zero_mul, Nat.zero_sub, Nat.zero_div,
        pow_zero, mul_one]
      have hcard : (Finset.univ : Finset (Fin 0 → W)).card = 1 := by simp
      exact (Finset.card_filter_le _ _).trans (le_of_eq hcard)
    | succ r =>
      have hempty : (Finset.univ.filter (fun w : Fin 0 → W =>
          (∀ i j, φ ((w i : K) * (w j : K)) = 0) ∧
          Module.finrank E (Submodule.span E (Set.range fun i => (w i : K))) = r + 1)) = ∅ := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro ⟨_, hfr⟩
        have hrange : Set.range (fun i : Fin 0 => (w i : K)) = ∅ := by simp
        rw [hrange, Submodule.span_empty, finrank_bot] at hfr
        omega
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
  | succ g ih =>
    intro r
    set S := Finset.univ.filter (fun w : Fin (g + 1) → W =>
      (∀ i j, φ ((w i : K) * (w j : K)) = 0) ∧
      Module.finrank E (Submodule.span E (Set.range fun i => (w i : K))) = r)
    by_cases h2rd : 2 * r ≤ d
    · rw [if_pos h2rd]
      let Sstay := S.filter (fun w =>
        (w (Fin.last g) : K) ∈ Submodule.span E (Set.range fun i : Fin g => (w i.castSucc : K)))
      let Sgrow := S.filter (fun w =>
        (w (Fin.last g) : K) ∉ Submodule.span E (Set.range fun i : Fin g => (w i.castSucc : K)))
      have hsplit : S.card = Sstay.card + Sgrow.card :=
        (Finset.card_filter_add_card_filter_not _).symm
      let A := Finset.univ.filter (fun w' : Fin g → W =>
        (∀ i j, φ ((w' i : K) * (w' j : K)) = 0) ∧
        Module.finrank E (Submodule.span E (Set.range fun i => (w' i : K))) = r)
      have hstay : Sstay.card ≤ q ^ r * A.card := by
        have hmap : Sstay.card = ∑ w' ∈ A, (Sstay.filter (fun w => Fin.init w = w')).card := by
          rw [← Finset.card_biUnion]
          · congr 1
            ext w
            simp only [Finset.mem_biUnion, Finset.mem_filter]
            constructor
            · intro hw
              refine ⟨Fin.init w, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hw, rfl⟩
              have hS := (Finset.mem_filter.1 hw).1
              have hmem := (Finset.mem_filter.1 hw).2
              have hiso := (Finset.mem_filter.1 hS).2.1
              have hfr := (Finset.mem_filter.1 hS).2.2
              refine ⟨fun i j => hiso i.castSucc j.castSucc, ?_⟩
              have hspan_eq : Submodule.span E (Set.range fun i : Fin g => (Fin.init w i : K)) =
                  Submodule.span E (Set.range fun i : Fin (g + 1) => (w i : K)) := by
                apply le_antisymm
                · exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j.castSucc, rfl⟩)
                · rw [Submodule.span_le]
                  rintro _ ⟨i, rfl⟩
                  refine Fin.lastCases ?_ (fun j => ?_) i
                  · exact hmem
                  · exact Submodule.subset_span ⟨j, rfl⟩
              rw [hspan_eq]
              exact hfr
            · rintro ⟨w', _, hw, _⟩
              exact hw
          · intro w1 _ w2 _ hne
            exact Finset.disjoint_left.2 fun w hw1 hw2 =>
              hne ((Finset.mem_filter.1 hw1).2.symm.trans (Finset.mem_filter.1 hw2).2)
        rw [hmap]
        calc ∑ w' ∈ A, (Sstay.filter (fun w => Fin.init w = w')).card
            ≤ ∑ _w' ∈ A, q ^ r := by
              refine Finset.sum_le_sum fun w' hw' => ?_
              have hfr' := (Finset.mem_filter.1 hw').2.2
              let U := Submodule.span E (Set.range fun i : Fin g => (w' i : K))
              let f : { w // w ∈ Sstay.filter (fun w => Fin.init w = w') } → U :=
                fun ⟨w, hw⟩ => ⟨(w (Fin.last g) : K), by
                  have h1 := (Finset.mem_filter.1 hw).1
                  have h2 := (Finset.mem_filter.1 hw).2
                  have hmem := (Finset.mem_filter.1 h1).2
                  have : (fun i : Fin g => (w i.castSucc : K)) = (fun i : Fin g => (w' i : K)) := by
                    ext i; exact congrArg (fun fn => (fn i : K)) h2
                  rwa [this] at hmem⟩
              have hf_inj : Function.Injective f := by
                rintro ⟨w1, hw1⟩ ⟨w2, hw2⟩ hfeq
                apply Subtype.ext
                ext i
                refine Fin.lastCases ?_ (fun j => ?_) i
                · exact congrArg (Subtype.val : U → K) hfeq
                · have h1 := (Finset.mem_filter.1 hw1).2
                  have h2 := (Finset.mem_filter.1 hw2).2
                  exact congrArg (fun fn => (fn j : K)) (h1.trans h2.symm)
              have hcard := Fintype.card_le_of_injective f hf_inj
              rw [Fintype.card_coe, card_submodule_eq_pow U] at hcard
              simpa [U, q, hfr'] using hcard
          _ = q ^ r * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      cases r with
      | zero =>
        have hgrow0 : Sgrow.card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro w hw
          have hS := (Finset.mem_filter.1 hw).1
          have hnot := (Finset.mem_filter.1 hw).2
          have hfr := (Finset.mem_filter.1 hS).2.2
          have hbot : Submodule.span E (Set.range fun i : Fin (g + 1) => (w i : K)) = ⊥ :=
            Submodule.finrank_eq_zero.1 hfr
          have h0 : (w (Fin.last g) : K) = 0 := by
            have : (w (Fin.last g) : K) ∈ Submodule.span E (Set.range fun i : Fin (g + 1) => (w i : K)) :=
              Submodule.subset_span ⟨Fin.last g, rfl⟩
            rwa [hbot, Submodule.mem_bot] at this
          rw [h0] at hnot
          exact hnot (Submodule.zero_mem _)
        rw [hsplit, hgrow0, add_zero]
        have hih := ih 0
        have hqb0 : qBinom q g 0 = 1 := by cases g <;> rfl
        have hqb1 : qBinom q (g + 1) 0 = 1 := rfl
        simp only [Nat.mul_zero, Nat.zero_le, ↓reduceIte, zero_mul, Nat.zero_sub, Nat.zero_div,
          pow_zero, mul_one, hqb0, hqb1] at hih ⊢
        calc Sstay.card ≤ 1 * A.card := by simpa using hstay
          _ = A.card := one_mul _
          _ ≤ 1 := hih
      | succ r =>
        let B := Finset.univ.filter (fun w' : Fin g → W =>
          (∀ i j, φ ((w' i : K) * (w' j : K)) = 0) ∧
          Module.finrank E (Submodule.span E (Set.range fun i => (w' i : K))) = r)
        have hgrow : Sgrow.card ≤ q ^ (d - r) * B.card := by
          have hmap : Sgrow.card = ∑ w' ∈ B, (Sgrow.filter (fun w => Fin.init w = w')).card := by
            rw [← Finset.card_biUnion]
            · congr 1
              ext w
              simp only [Finset.mem_biUnion, Finset.mem_filter]
              constructor
              · intro hw
                refine ⟨Fin.init w, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hw, rfl⟩
                have hS := (Finset.mem_filter.1 hw).1
                have hnot := (Finset.mem_filter.1 hw).2
                have hiso := (Finset.mem_filter.1 hS).2.1
                have hfr := (Finset.mem_filter.1 hS).2.2
                refine ⟨fun i j => hiso i.castSucc j.castSucc, ?_⟩
                let U := Submodule.span E (Set.range fun i : Fin g => (w i.castSucc : K))
                let L := Submodule.span E {(w (Fin.last g) : K)}
                have hsup : Submodule.span E (Set.range fun i : Fin (g + 1) => (w i : K)) = U ⊔ L := by
                  apply le_antisymm
                  · rw [Submodule.span_le]
                    rintro _ ⟨i, rfl⟩
                    refine Fin.lastCases ?_ (fun j => ?_) i
                    · exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
                    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩)
                  · refine sup_le (Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j.castSucc, rfl⟩)) ?_
                    rw [Submodule.span_singleton_le_iff_mem]
                    exact Submodule.subset_span ⟨Fin.last g, rfl⟩
                have hinf : U ⊓ L = ⊥ := by
                  rw [Submodule.eq_bot_iff]
                  intro x ⟨hxU, hxL⟩
                  have hxL' : x ∈ Submodule.span E {(w (Fin.last g) : K)} := hxL
                  rw [Submodule.mem_span_singleton] at hxL'
                  obtain ⟨c, rfl⟩ := hxL'
                  by_cases hc : c = 0
                  · simp [hc]
                  · exfalso
                    apply hnot
                    have : c⁻¹ • (c • (w (Fin.last g) : K)) ∈ U := U.smul_mem c⁻¹ hxU
                    simpa [smul_smul, inv_mul_cancel₀ hc] using this
                have hLne : (w (Fin.last g) : K) ≠ 0 := fun h0 => hnot (h0 ▸ Submodule.zero_mem _)
                have hLfr : Module.finrank E L = 1 := finrank_span_singleton hLne
                have hadd := Submodule.finrank_sup_add_finrank_inf_eq U L
                rw [← hsup, hfr, hinf, finrank_bot, add_zero, hLfr] at hadd
                have hUfr : Module.finrank E U = r := by omega
                exact hUfr
              · rintro ⟨w', _, hw, _⟩
                exact hw
            · intro w1 _ w2 _ hne
              exact Finset.disjoint_left.2 fun w hw1 hw2 =>
                hne ((Finset.mem_filter.1 hw1).2.symm.trans (Finset.mem_filter.1 hw2).2)
          rw [hmap]
          calc ∑ w' ∈ B, (Sgrow.filter (fun w => Fin.init w = w')).card
              ≤ ∑ _w' ∈ B, q ^ (d - r) := by
                refine Finset.sum_le_sum fun w' hw' => ?_
                have hfr' := (Finset.mem_filter.1 hw').2.2
                let U := Submodule.span E (Set.range fun i : Fin g => (w' i : K))
                have hUW : U ≤ W := by
                  rw [Submodule.span_le]
                  rintro _ ⟨i, rfl⟩
                  exact (w' i).2
                let P : Submodule E K := W ⊓ perpSub φ U
                have hPfr : Module.finrank E P = d - r := by
                  have h := finrank_inter_perpSub_of_nondeg φ W U hnondeg hUW
                  change Module.finrank E U + Module.finrank E P = d at h
                  change Module.finrank E U = r at hfr'
                  omega
                let f : { w // w ∈ Sgrow.filter (fun w => Fin.init w = w') } → P :=
                  fun ⟨w, hw⟩ => ⟨(w (Fin.last g) : K), by
                    have h1 := (Finset.mem_filter.1 hw).1
                    have h2 := (Finset.mem_filter.1 hw).2
                    have hS := (Finset.mem_filter.1 h1).1
                    have hiso := (Finset.mem_filter.1 hS).2.1
                    refine ⟨(w (Fin.last g)).2, ?_⟩
                    intro x hx
                    induction hx using Submodule.span_induction with
                    | mem y hy =>
                      obtain ⟨i, rfl⟩ := hy
                      have hwi : (w' i : K) = (w i.castSucc : K) :=
                        congrArg (fun fn => (fn i : K)) h2.symm
                      change φ ((w' i : K) * (w (Fin.last g) : K)) = 0
                      rw [hwi]
                      exact hiso i.castSucc (Fin.last g)
                    | zero => simp
                    | add a b _ _ iha ihb =>
                      have ha : φ (a * (w (Fin.last g) : K)) = 0 := iha
                      have hb : φ (b * (w (Fin.last g) : K)) = 0 := ihb
                      change φ ((a + b) * (w (Fin.last g) : K)) = 0
                      rw [add_mul, map_add, ha, hb, add_zero]
                    | smul c a _ iha =>
                      have ha : φ (a * (w (Fin.last g) : K)) = 0 := iha
                      change φ ((c • a) * (w (Fin.last g) : K)) = 0
                      rw [smul_mul_assoc, map_smul, ha, smul_zero]⟩
                have hf_inj : Function.Injective f := by
                  rintro ⟨w1, hw1⟩ ⟨w2, hw2⟩ hfeq
                  apply Subtype.ext
                  ext i
                  refine Fin.lastCases ?_ (fun j => ?_) i
                  · exact congrArg (Subtype.val : P → K) hfeq
                  · have h1 := (Finset.mem_filter.1 hw1).2
                    have h2 := (Finset.mem_filter.1 hw2).2
                    exact congrArg (fun fn => (fn j : K)) (h1.trans h2.symm)
                have hcard := Fintype.card_le_of_injective f hf_inj
                rw [Fintype.card_coe, card_submodule_eq_pow P] at hcard
                simpa [P, q, hPfr] using hcard
            _ = q ^ (d - r) * B.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        have hihA := ih (r + 1)
        have hihB := ih r
        rw [if_pos h2rd] at hihA
        rw [if_pos (by omega : 2 * r ≤ d)] at hihB
        have hexp : (d - r) + (r * d - r * (r - 1) / 2) = (r + 1) * d - (r + 1) * r / 2 := by
          have he1 := even_mul_pred r
          have he2 := even_mul_succ r
          have htri : (r + 1) * r = r * (r - 1) + 2 * r := by
            cases r with
            | zero => simp
            | succ r' => simp only [Nat.add_sub_cancel]; ring
          have hle1 : r * (r - 1) ≤ 2 * (r * d) := by
            cases r with
            | zero => simp
            | succ r' => simp only [Nat.add_sub_cancel]; nlinarith
          have hmul : (r + 1) * d = d + r * d := by ring
          omega
        calc S.card = Sstay.card + Sgrow.card := hsplit
          _ ≤ q ^ (r + 1) * A.card + q ^ (d - r) * B.card := Nat.add_le_add hstay hgrow
          _ ≤ q ^ (r + 1) * (qBinom q g (r + 1) * q ^ ((r + 1) * d - (r + 1) * r / 2)) +
              q ^ (d - r) * (qBinom q g r * q ^ (r * d - r * (r - 1) / 2)) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hihA) (Nat.mul_le_mul_left _ hihB)
          _ = q ^ (r + 1) * qBinom q g (r + 1) * q ^ ((r + 1) * d - (r + 1) * r / 2) +
              qBinom q g r * (q ^ (d - r) * q ^ (r * d - r * (r - 1) / 2)) := by ring
          _ = (q ^ (r + 1) * qBinom q g (r + 1) + qBinom q g r) *
              q ^ ((r + 1) * d - (r + 1) * r / 2) := by rw [← pow_add, hexp]; ring
          _ = qBinom q (g + 1) (r + 1) * q ^ ((r + 1) * d - (r + 1) * r / 2) := by rfl
    · rw [if_neg h2rd]
      have hempty : S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro w hw
        have hiso := (Finset.mem_filter.1 hw).2.1
        have hfr := (Finset.mem_filter.1 hw).2.2
        let U := Submodule.span E (Set.range fun i : Fin (g + 1) => (w i : K))
        have hUW : U ≤ W := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact (w i).2
        have hUperp : U ≤ W ⊓ perpSub φ U := by
          refine le_inf hUW ?_
          rw [Submodule.span_le]
          rintro _ ⟨j, rfl⟩ x hx
          induction hx using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨i, rfl⟩ := hy
            exact hiso i j
          | zero => simp
          | add a b _ _ iha ihb =>
            change φ ((a + b) * (w j : K)) = 0
            rw [add_mul, map_add, iha, ihb, add_zero]
          | smul c a _ iha =>
            change φ ((c • a) * (w j : K)) = 0
            rw [smul_mul_assoc, map_smul, iha, smul_zero]
        have hle := Submodule.finrank_mono hUperp
        have heq := finrank_inter_perpSub_of_nondeg φ W U hnondeg hUW
        change Module.finrank E U = r at hfr
        change Module.finrank E U + Module.finrank E (W ⊓ perpSub φ U : Submodule E K) = d at heq
        omega
      rw [hempty, Finset.card_empty]

private theorem exists_spanning_directions (h m g : ℕ) (hh : 2 ≤ h) (hm : 0 < m)
    (hmg : m ≤ g * (g + 1) / 2)
    (K : Type) [Field K] [Algebra (ZMod 2) K] [Algebra (GaloisField 2 h) K]
    [IsScalarTower (ZMod 2) (GaloisField 2 h) K]
    [FiniteDimensional (GaloisField 2 h) K] [Fintype K]
    (hfrK : Module.finrank (GaloisField 2 h) K = m) :
    ∃ d : Fin g → K,
      Submodule.span (GaloisField 2 h) (Set.range fun p : Fin g × Fin g => d p.1 * d p.2) = ⊤ := by
  classical
  let E := GaloisField 2 h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype E := Fintype.ofFinite E
  haveI : Finite (K →ₗ[E] E) := Finite.of_injective (fun f : K →ₗ[E] E => (f : K → E)) DFunLike.coe_injective
  letI : Fintype (K →ₗ[E] E) := Fintype.ofFinite (K →ₗ[E] E)
  have hcardE : Fintype.card E = 2 ^ h :=
    (Nat.card_eq_fintype_card (α := E)).symm.trans (GaloisField.card 2 h (by omega))
  set q := Fintype.card E
  have hq4 : 4 ≤ q := by
    rw [hcardE]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) hh
  haveI : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hcardK : Fintype.card K = q ^ m := by
    rw [Module.card_eq_pow_finrank (K := E) (V := K), hfrK]
  have hsq_add : ∀ x y : K, (x + y) * (x + y) = x * x + y * y := by
    intro x y
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination (x * y) * h2
  have hsq_bij : Function.Bijective (fun x : K => x * x) := by
    apply Finite.injective_iff_bijective.1
    intro x y hxy
    have h0 : (x - y) * (x - y) = 0 := by
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have hxy' : x * x = y * y := hxy
      have hsub2 : (x - y) * (x - y) = x * x - 2 * (x * y) + y * y := by ring
      rw [hsub2, h2, zero_mul, sub_zero, hxy']
      linear_combination (y * y) * h2
    have hsub : x - y = 0 := by
      rcases mul_eq_zero.1 h0 with h | h <;> exact h
    exact sub_eq_zero.1 hsub
  let BadPhi : (K →ₗ[E] E) → Finset (Fin g → K) := fun φ =>
    Finset.univ.filter (fun d : Fin g → K => ∀ i j, φ (d i * d j) = 0)
  have hBadPhi_bound : ∀ φ : K →ₗ[E] E, φ ≠ 0 →
      (q ^ m - 1) * (BadPhi φ).card < (q - 1) * q ^ (m * g) := by
    intro φ hφ
    let H : Submodule E K :=
      { carrier := { x : K | φ (x * x) = 0 }, add_mem' := fun hx hy => by
          show φ ((_ + _) * (_ + _)) = 0
          rw [hsq_add, map_add, hx, hy, add_zero]
        zero_mem' := by simp
        smul_mem' := fun c x hx => by
          show φ ((c • x) * (c • x)) = 0
          have : (c • x) * (c • x) = (c * c) • (x * x) := by
            simp only [Algebra.smul_def, map_mul]; ring
          rw [this, map_smul, hx, smul_zero] }
    have hHcard : Fintype.card H = Fintype.card (LinearMap.ker φ) := by
      refine Fintype.card_of_bijective (f := fun x : H => (⟨x.1 * x.1, x.2⟩ : LinearMap.ker φ)) ?_
      constructor
      · rintro ⟨x, hx⟩ ⟨y, hy⟩ heq
        apply Subtype.ext
        exact hsq_bij.1 (congrArg Subtype.val heq)
      · rintro ⟨y, hy⟩
        obtain ⟨x, hx⟩ := hsq_bij.2 y
        have hx' : x * x = y := hx
        exact ⟨⟨x, by show φ (x * x) = 0; rw [hx']; exact hy⟩, Subtype.ext hx'⟩
    have hkerφ_fr : Module.finrank E (LinearMap.ker φ) = m - 1 := by
      have hrn := LinearMap.finrank_range_add_finrank_ker φ
      rw [hfrK] at hrn
      have hrange : Module.finrank E (LinearMap.range φ) = 1 := by
        have hle : Module.finrank E (LinearMap.range φ) ≤ 1 := by
          simpa using Submodule.finrank_le (LinearMap.range φ)
        have hpos : 0 < Module.finrank E (LinearMap.range φ) := by
          by_contra h0
          have hbot : LinearMap.range φ = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
          apply hφ
          ext x
          have : φ x ∈ LinearMap.range φ := ⟨x, rfl⟩
          rwa [hbot, Submodule.mem_bot] at this
        omega
      omega
    have hHfr : Module.finrank E H = m - 1 := by
      rw [card_submodule_eq_pow H, card_submodule_eq_pow (LinearMap.ker φ), hkerφ_fr] at hHcard
      exact Nat.pow_right_injective (by omega : 2 ≤ q) hHcard
    let R : Submodule E K := H ⊓ perpSub φ H
    have hRle : Module.finrank E R ≤ 1 := by
      have h1 := finrank_perpSub φ hφ H
      rw [hfrK, hHfr] at h1
      have h2 : Module.finrank E R ≤ Module.finrank E (perpSub φ H) :=
        Submodule.finrank_mono inf_le_right
      omega
    let R' : Submodule E H := R.comap H.subtype
    obtain ⟨W', hRW'⟩ := Submodule.exists_isCompl R'
    let W : Submodule E K := W'.map H.subtype
    have hRW_inf : R ⊓ W = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x ⟨hxR, hxW⟩
      obtain ⟨⟨w, hwH⟩, hwW', rfl⟩ := hxW
      have hwR' : ⟨w, hwH⟩ ∈ R' := hxR
      have : (⟨w, hwH⟩ : H) ∈ R' ⊓ W' := ⟨hwR', hwW'⟩
      rw [hRW'.inf_eq_bot, Submodule.mem_bot] at this
      exact congrArg Subtype.val this
    have hRW_sup : R ⊔ W = H := by
      apply le_antisymm
      · refine sup_le inf_le_left ?_
        rintro _ ⟨⟨w, hwH⟩, _, rfl⟩; exact hwH
      · intro x hxH
        have hmem : (⟨x, hxH⟩ : H) ∈ R' ⊔ W' := by rw [hRW'.sup_eq_top]; trivial
        rw [Submodule.mem_sup] at hmem
        obtain ⟨r, hr, w, hw, heq⟩ := hmem
        have hsum : r.1 + w.1 = x := congrArg Subtype.val heq
        rw [← hsum]
        exact Submodule.add_mem_sup hr ⟨w, hw, rfl⟩
    have hWnondeg : W ⊓ perpSub φ W = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x ⟨hxW, hxperpW⟩
      have hxH : x ∈ H := by rw [← hRW_sup]; exact Submodule.mem_sup_right hxW
      have hxperpH : x ∈ perpSub φ H := by
        intro y hyH
        rw [← hRW_sup, Submodule.mem_sup] at hyH
        obtain ⟨r, hr, w, hw, rfl⟩ := hyH
        rw [add_mul, map_add]
        have hr0 : φ (r * x) = 0 := by rw [mul_comm]; exact hr.2 x hxH
        have hw0 : φ (w * x) = 0 := hxperpW w hw
        rw [hr0, hw0, add_zero]
      have hxR : x ∈ R := ⟨hxH, hxperpH⟩
      have : x ∈ R ⊓ W := ⟨hxR, hxW⟩
      rwa [hRW_inf] at this
    have hRW_fr : Module.finrank E R + Module.finrank E W = m - 1 := by
      have := Submodule.finrank_sup_add_finrank_inf_eq R W
      rw [hRW_sup, hRW_inf, finrank_bot, add_zero, hHfr] at this
      exact this.symm
    set dimR := Module.finrank E R
    set d := Module.finrank E W
    have hd_eq : d = m - 1 - dimR := by omega
    have hdimRm : dimR + 1 ≤ m := by omega
    have hBadCard : (BadPhi φ).card ≤ q ^ (g * dimR) *
        (Finset.univ.filter (fun w : Fin g → W => ∀ i j, φ ((w i : K) * (w j : K)) = 0)).card := by
      let Wiso := Finset.univ.filter (fun w : Fin g → W => ∀ i j, φ ((w i : K) * (w j : K)) = 0)
      let f : { u // u ∈ BadPhi φ } → (Fin g → R) × { w // w ∈ Wiso } := fun ⟨u, hu⟩ =>
        have huH : ∀ i, u i ∈ H := fun i => (Finset.mem_filter.1 hu).2 i i
        let pr : Fin g → R × W := fun i =>
          (Submodule.prodEquivOfIsCompl R' W' hRW').symm ⟨u i, huH i⟩ |>.map
            (fun r => ⟨r.1.1, r.2⟩) (fun w => ⟨w.1.1, ⟨w.1, w.2, rfl⟩⟩)
        (fun i => (pr i).1, ⟨fun i => (pr i).2, by
          simp only [Wiso, Finset.mem_filter, Finset.mem_univ, true_and]
          intro i j
          have hdecomp : ∀ t : Fin g, u t = ((pr t).1 : K) + ((pr t).2 : K) := fun t => by
            let p := (Submodule.prodEquivOfIsCompl R' W' hRW').symm ⟨u t, huH t⟩
            have hp : (p.1 : H) + (p.2 : H) = ⟨u t, huH t⟩ :=
              (Submodule.prodEquivOfIsCompl R' W' hRW').apply_symm_apply ⟨u t, huH t⟩
            exact (congrArg Subtype.val hp).symm
          have hij := (Finset.mem_filter.1 hu).2 i j
          rw [hdecomp i, hdecomp j] at hij
          have hr1 : φ (((pr i).1 : K) * ((pr j).1 : K)) = 0 := by
            rw [mul_comm]; exact (pr i).1.2.2 _ (pr j).1.2.1
          have hr2 : φ (((pr i).1 : K) * ((pr j).2 : K)) = 0 := by
            rw [mul_comm]
            exact (pr i).1.2.2 _ (by rw [← hRW_sup]; exact Submodule.mem_sup_right (pr j).2.2)
          have hr3 : φ (((pr i).2 : K) * ((pr j).1 : K)) = 0 := by
            exact (pr j).1.2.2 _ (by rw [← hRW_sup]; exact Submodule.mem_sup_right (pr i).2.2)
          rw [add_mul, mul_add, mul_add, map_add, map_add, map_add, hr1, hr2, hr3] at hij
          simpa using hij⟩)
      have hf_inj : Function.Injective f := by
        rintro ⟨u1, hu1⟩ ⟨u2, hu2⟩ hfeq
        apply Subtype.ext
        ext i
        have hu1H : ∀ t, u1 t ∈ H := fun t => (Finset.mem_filter.1 hu1).2 t t
        have hu2H : ∀ t, u2 t ∈ H := fun t => (Finset.mem_filter.1 hu2).2 t t
        have hdecomp1 : u1 i = ((f ⟨u1, hu1⟩).1 i : K) + (((f ⟨u1, hu1⟩).2.1 i) : K) := by
          let p := (Submodule.prodEquivOfIsCompl R' W' hRW').symm ⟨u1 i, hu1H i⟩
          have hp : (p.1 : H) + (p.2 : H) = ⟨u1 i, hu1H i⟩ :=
            (Submodule.prodEquivOfIsCompl R' W' hRW').apply_symm_apply ⟨u1 i, hu1H i⟩
          exact (congrArg Subtype.val hp).symm
        have hdecomp2 : u2 i = ((f ⟨u2, hu2⟩).1 i : K) + (((f ⟨u2, hu2⟩).2.1 i) : K) := by
          let p := (Submodule.prodEquivOfIsCompl R' W' hRW').symm ⟨u2 i, hu2H i⟩
          have hp : (p.1 : H) + (p.2 : H) = ⟨u2 i, hu2H i⟩ :=
            (Submodule.prodEquivOfIsCompl R' W' hRW').apply_symm_apply ⟨u2 i, hu2H i⟩
          exact (congrArg Subtype.val hp).symm
        change u1 i = u2 i
        rw [hdecomp1, hdecomp2, hfeq]
      have hcard := Fintype.card_le_of_injective f hf_inj
      rw [Fintype.card_coe, Fintype.card_prod, Fintype.card_pi, Fintype.card_coe] at hcard
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcard
      rw [card_submodule_eq_pow R, ← pow_mul, mul_comm dimR g] at hcard
      exact hcard
    set rmax := min g (d / 2)
    have hWiso_bound : (Finset.univ.filter (fun w : Fin g → W => ∀ i j, φ ((w i : K) * (w j : K)) = 0)).card ≤
        ∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2) := by
      let Wiso := Finset.univ.filter (fun w : Fin g → W => ∀ i j, φ ((w i : K) * (w j : K)) = 0)
      let WisoR : ℕ → Finset (Fin g → W) := fun r =>
        Finset.univ.filter (fun w : Fin g → W =>
          (∀ i j, φ ((w i : K) * (w j : K)) = 0) ∧
          Module.finrank E (Submodule.span E (Set.range fun i => (w i : K))) = r)
      have hpart : Wiso ⊆ (Finset.range (rmax + 1)).biUnion WisoR := by
        intro w hw
        have hiso := (Finset.mem_filter.1 hw).2
        let U := Submodule.span E (Set.range fun i : Fin g => (w i : K))
        have hUW : U ≤ W := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact (w i).2
        have hUperp : U ≤ W ⊓ perpSub φ U := by
          refine le_inf hUW ?_
          rw [Submodule.span_le]
          rintro _ ⟨j, rfl⟩ x hx
          induction hx using Submodule.span_induction with
          | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hiso i j
          | zero => simp
          | add a b _ _ iha ihb => rw [add_mul, map_add, iha, ihb, add_zero]
          | smul c a _ iha => rw [smul_mul_assoc, map_smul, iha, smul_zero]
        have hle1 : Module.finrank E U ≤ g := by
          have hrange : Set.range (fun i : Fin g => (w i : K)) =
              ((Finset.univ.image (fun i : Fin g => (w i : K)) : Finset K) : Set K) := by
            ext x; simp
          have h1 : Module.finrank E U ≤ (Finset.univ.image (fun i : Fin g => (w i : K))).card := by
            change Module.finrank E (Submodule.span E (Set.range fun i : Fin g => (w i : K))) ≤ _
            rw [hrange]
            simpa using finrank_span_le_card ((Finset.univ.image (fun i : Fin g => (w i : K)) : Finset K) : Set K)
          exact h1.trans (Finset.card_image_le.trans (by simp))
        have hle2 : 2 * Module.finrank E U ≤ d := by
          have h1 := Submodule.finrank_mono hUperp
          have h2 := finrank_inter_perpSub_of_nondeg φ W U hWnondeg hUW
          change Module.finrank E U + Module.finrank E (W ⊓ perpSub φ U : Submodule E K) = d at h2
          omega
        refine Finset.mem_biUnion.2 ⟨Module.finrank E U, Finset.mem_range.2 (by omega), ?_⟩
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hiso, rfl⟩
      calc Wiso.card
          ≤ ((Finset.range (rmax + 1)).biUnion WisoR).card := Finset.card_le_card hpart
        _ ≤ ∑ r ∈ Finset.range (rmax + 1), (WisoR r).card := Finset.card_biUnion_le
        _ ≤ ∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2) := by
            refine Finset.sum_le_sum fun r hr => ?_
            rw [Finset.mem_range] at hr
            have h := card_iso_tuples_nondeg φ W hWnondeg g r
            rw [if_pos (by omega : 2 * r ≤ d)] at h
            exact h
    have harith := union_bound_arith q m g dimR hq4 hm hmg hRle hdimRm
    rw [← hd_eq] at harith
    calc (q ^ m - 1) * (BadPhi φ).card
        ≤ (q ^ m - 1) * (q ^ (g * dimR) *
            (∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2))) :=
          Nat.mul_le_mul_left _ (hBadCard.trans (Nat.mul_le_mul_left _ hWiso_bound))
      _ = (q ^ m - 1) * q ^ (g * dimR) *
            (∑ r ∈ Finset.range (rmax + 1), qBinom q g r * q ^ (r * d - r * (r - 1) / 2)) := by ring
      _ < (q - 1) * q ^ (m * g) := harith
  let DualNZ : Finset (K →ₗ[E] E) := Finset.univ.filter (fun φ => φ ≠ 0)
  have hDualCard : DualNZ.card = q ^ m - 1 := by
    have htot : Fintype.card (K →ₗ[E] E) = q ^ m := by
      rw [Module.card_eq_pow_finrank (K := E) (V := K →ₗ[E] E), Module.finrank_linearMap,
        Module.finrank_self, mul_one, hfrK]
    have h0 : (Finset.univ.filter (fun φ : K →ₗ[E] E => φ = 0)).card = 1 := by
      have : Finset.univ.filter (fun φ : K →ₗ[E] E => φ = 0) = {0} := by ext φ; simp
      rw [this, Finset.card_singleton]
    have hadd := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (K →ₗ[E] E)))
      (p := fun φ => φ = 0)
    simp only [Finset.card_univ, htot, h0] at hadd
    change DualNZ.card = q ^ m - 1
    have : Finset.univ.filter (fun φ : K →ₗ[E] E => ¬φ = 0) = DualNZ := rfl
    rw [this] at hadd
    omega
  let Bad : Finset (Fin g → K) := Finset.univ.filter (fun d => ∃ φ ∈ DualNZ, d ∈ BadPhi φ)
  have hdouble : (q - 1) * Bad.card ≤ ∑ φ ∈ DualNZ, (BadPhi φ).card := by
    let pairs := DualNZ.biUnion (fun φ => (BadPhi φ).image (fun d => (φ, d)))
    have hp1 : pairs.card = ∑ φ ∈ DualNZ, (BadPhi φ).card := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun φ _ => Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
      · intro φ1 _ φ2 _ hne
        exact Finset.disjoint_left.2 fun p hp1 hp2 => by
          obtain ⟨_, _, rfl⟩ := Finset.mem_image.1 hp1
          obtain ⟨_, _, heq⟩ := Finset.mem_image.1 hp2
          exact hne (Prod.mk.inj heq).1.symm
    rw [← hp1]
    have hp2 : (q - 1) * Bad.card ≤ ∑ d ∈ Bad, (pairs.filter (fun p => p.2 = d)).card := by
      calc (q - 1) * Bad.card = ∑ _d ∈ Bad, (q - 1) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ d ∈ Bad, (pairs.filter (fun p => p.2 = d)).card := by
            refine Finset.sum_le_sum fun d hd => ?_
            obtain ⟨φ, hφNZ, hdφ⟩ := (Finset.mem_filter.1 hd).2
            have hφ0 : φ ≠ 0 := (Finset.mem_filter.1 hφNZ).2
            let unitsE : Finset E := Finset.univ.filter (fun c : E => c ≠ 0)
            have hunits : unitsE.card = q - 1 := by
              have h0 : (Finset.univ.filter (fun c : E => c = 0)).card = 1 := by
                have : Finset.univ.filter (fun c : E => c = 0) = {0} := by ext c; simp
                rw [this, Finset.card_singleton]
              have hadd := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset E))
                (p := fun c => c = 0)
              simp only [Finset.card_univ, h0] at hadd
              have : Finset.univ.filter (fun c : E => ¬c = 0) = unitsE := rfl
              rw [this] at hadd
              omega
            rw [← hunits]
            let img := unitsE.image (fun c => (c • φ, d))
            have himg_sub : img ⊆ pairs.filter (fun p => p.2 = d) := by
              intro p hp
              obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
              have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
              refine Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨c • φ, ?_, ?_⟩, rfl⟩
              · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
                intro hzero
                apply hφ0
                have : c⁻¹ • (c • φ) = 0 := by rw [hzero, smul_zero]
                rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
              · refine Finset.mem_image.2 ⟨d, ?_, rfl⟩
                refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i j => ?_⟩
                simp [(Finset.mem_filter.1 hdφ).2 i j]
            have himg_card : img.card = unitsE.card := by
              refine Finset.card_image_of_injective _ fun c1 c2 heq => ?_
              have hsmul : c1 • φ = c2 • φ := (Prod.mk.inj heq).1
              have hex : ∃ x : K, φ x ≠ 0 := by
                by_contra hall; push Not at hall; exact hφ0 (LinearMap.ext hall)
              obtain ⟨x, hx⟩ := hex
              have hval : c1 * φ x = c2 * φ x := by
                have := congrArg (fun f : K →ₗ[E] E => f x) hsmul
                simpa using this
              exact mul_right_cancel₀ hx hval
            rw [← himg_card]
            exact Finset.card_le_card himg_sub
    refine hp2.trans ?_
    have hdisj : (Bad.biUnion (fun d => pairs.filter (fun p => p.2 = d))).card =
        ∑ d ∈ Bad, (pairs.filter (fun p => p.2 = d)).card := by
      rw [Finset.card_biUnion]
      intro d1 _ d2 _ hne
      exact Finset.disjoint_left.2 fun p hp1 hp2 =>
        hne ((Finset.mem_filter.1 hp1).2.symm.trans (Finset.mem_filter.1 hp2).2)
    rw [← hdisj]
    exact Finset.card_le_card (Finset.biUnion_subset.2 fun _ _ => Finset.filter_subset _ _)
  have hsum_lt : ∑ φ ∈ DualNZ, (BadPhi φ).card < (q - 1) * q ^ (m * g) := by
    by_cases hne : DualNZ.Nonempty
    · obtain ⟨φ0, hφ0, hmax⟩ := DualNZ.exists_max_image (fun φ => (BadPhi φ).card) hne
      calc ∑ φ ∈ DualNZ, (BadPhi φ).card
          ≤ ∑ _φ ∈ DualNZ, (BadPhi φ0).card := Finset.sum_le_sum hmax
        _ = (q ^ m - 1) * (BadPhi φ0).card := by rw [Finset.sum_const, smul_eq_mul, hDualCard]
        _ < (q - 1) * q ^ (m * g) := hBadPhi_bound φ0 (Finset.mem_filter.1 hφ0).2
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
      exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have hBad_lt : Bad.card < Fintype.card (Fin g → K) := by
    have hcard_all : Fintype.card (Fin g → K) = q ^ (m * g) := by
      rw [Fintype.card_pi]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcardK, ← pow_mul]
    rw [hcard_all]
    have hlt : (q - 1) * Bad.card < (q - 1) * q ^ (m * g) := lt_of_le_of_lt hdouble hsum_lt
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hex : ∃ d : Fin g → K, d ∉ Bad := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin g → K)) ⊆ Bad := fun d _ => hall d
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ] at hle
    omega
  obtain ⟨d, hd⟩ := hex
  refine ⟨d, ?_⟩
  by_contra hnotTop
  let U := Submodule.span E (Set.range fun p : Fin g × Fin g => d p.1 * d p.2)
  obtain ⟨V, hUV⟩ := Submodule.exists_isCompl U
  have hVne : V ≠ ⊥ := by
    intro hVbot
    apply hnotTop
    have := hUV.sup_eq_top
    rwa [hVbot, sup_bot_eq] at this
  obtain ⟨v, hvV, hv0⟩ : ∃ v ∈ V, v ≠ 0 := by
    by_contra hall; push Not at hall
    apply hVne
    rw [Submodule.eq_bot_iff]
    exact fun x hx => hall x hx
  let L := Submodule.span E {v}
  have hLV : L ≤ V := by rw [Submodule.span_singleton_le_iff_mem]; exact hvV
  let L' : Submodule E V := L.comap V.subtype
  obtain ⟨W', hLW'⟩ := Submodule.exists_isCompl L'
  let e1 := Submodule.prodEquivOfIsCompl U V hUV
  let e2 := Submodule.prodEquivOfIsCompl L' W' hLW'
  let projV : K →ₗ[E] V := (LinearMap.snd E U V).comp e1.symm.toLinearMap
  let projL' : V →ₗ[E] L' := (LinearMap.fst E L' W').comp e2.symm.toLinearMap
  let coord : L' →ₗ[E] E :=
    { toFun := fun x => Classical.choose (Submodule.mem_span_singleton.1 x.2)
      map_add' := fun x y => by
        have hx := Classical.choose_spec (Submodule.mem_span_singleton.1 x.2)
        have hy := Classical.choose_spec (Submodule.mem_span_singleton.1 y.2)
        have hxy := Classical.choose_spec (Submodule.mem_span_singleton.1 (x + y).2)
        have hsmul : (Classical.choose (Submodule.mem_span_singleton.1 (x + y).2)) • v =
            (Classical.choose (Submodule.mem_span_singleton.1 x.2) +
             Classical.choose (Submodule.mem_span_singleton.1 y.2)) • v := by
          rw [add_smul, hx, hy, hxy]; rfl
        have hdiff : (Classical.choose (Submodule.mem_span_singleton.1 (x + y).2) -
            (Classical.choose (Submodule.mem_span_singleton.1 x.2) +
             Classical.choose (Submodule.mem_span_singleton.1 y.2))) • v = 0 := by
          rw [sub_smul, hsmul, sub_self]
        rcases smul_eq_zero.1 hdiff with h | h
        · exact sub_eq_zero.1 h
        · exact False.elim (hv0 h)
      map_smul' := fun c x => by
        have hx := Classical.choose_spec (Submodule.mem_span_singleton.1 x.2)
        have hcx := Classical.choose_spec (Submodule.mem_span_singleton.1 (c • x).2)
        have hsmul : (Classical.choose (Submodule.mem_span_singleton.1 (c • x).2)) • v =
            (c * Classical.choose (Submodule.mem_span_singleton.1 x.2)) • v := by
          rw [mul_smul, hx, hcx]; rfl
        have hdiff : (Classical.choose (Submodule.mem_span_singleton.1 (c • x).2) -
            c * Classical.choose (Submodule.mem_span_singleton.1 x.2)) • v = 0 := by
          rw [sub_smul, hsmul, sub_self]
        rcases smul_eq_zero.1 hdiff with h | h
        · exact sub_eq_zero.1 h
        · exact False.elim (hv0 h) }
  let φ : K →ₗ[E] E := coord.comp (projL'.comp projV)
  have hφ_ne : φ ≠ 0 := by
    intro h0
    have hval : φ v = 1 := by
      have he1 : e1 ((0 : U), ⟨v, hvV⟩) = v := by simp [e1]
      have hsymm1 : e1.symm v = ((0 : U), ⟨v, hvV⟩) := e1.symm_apply_eq.2 he1.symm
      have hvL' : (⟨v, hvV⟩ : V) ∈ L' := Submodule.subset_span (Set.mem_singleton v)
      have he2 : e2 (⟨⟨v, hvV⟩, hvL'⟩, (0 : W')) = ⟨v, hvV⟩ := by simp [e2]
      have hsymm2 : e2.symm ⟨v, hvV⟩ = (⟨⟨v, hvV⟩, hvL'⟩, (0 : W')) := e2.symm_apply_eq.2 he2.symm
      have hspec : (Classical.choose (Submodule.mem_span_singleton.1 hvL')) • v = v :=
        Classical.choose_spec (Submodule.mem_span_singleton.1 hvL')
      have hdiff : (Classical.choose (Submodule.mem_span_singleton.1 hvL') - 1) • v = 0 := by
        rw [sub_smul, one_smul, hspec, sub_self]
      have h1 : Classical.choose (Submodule.mem_span_singleton.1 hvL') = 1 := by
        rcases smul_eq_zero.1 hdiff with h | h
        · exact sub_eq_zero.1 h
        · exact False.elim (hv0 h)
      simpa [φ, projV, projL', coord, hsymm1, hsymm2] using h1
    rw [h0] at hval
    simp at hval
  have hφ_zero : ∀ i j : Fin g, φ (d i * d j) = 0 := by
    intro i j
    have hmem : d i * d j ∈ U := Submodule.subset_span ⟨(i, j), rfl⟩
    have he1 : e1 (⟨d i * d j, hmem⟩, (0 : V)) = d i * d j := by simp [e1]
    have hsymm1 : e1.symm (d i * d j) = (⟨d i * d j, hmem⟩, (0 : V)) := e1.symm_apply_eq.2 he1.symm
    simp [φ, projV, hsymm1]
  apply hd
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, φ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hφ_ne⟩, ?_⟩
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hφ_zero⟩

private theorem lift_bit_to_E (h : ℕ) (hh : 2 ≤ h)
    (K : Type) [Field K] [Algebra (ZMod 2) K] [Algebra (GaloisField 2 h) K]
    [IsScalarTower (ZMod 2) (GaloisField 2 h) K]
    [FiniteDimensional (GaloisField 2 h) K]
    (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) :
    let F := ZMod 2
    let E := GaloisField 2 h
    ∃ (eBasis : Module.Basis (Fin h) F E) (τ : E →ₗ[F] F) (Ψ : K →ₗ[E] E),
      Ψ ≠ 0 ∧ ∀ (c : E) (w : K), bit (c • w) = τ (c * Ψ w) := by
  classical
  let F := ZMod 2
  let E := GaloisField 2 h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype E := Fintype.ofFinite E
  have hcardE : Fintype.card E = 2 ^ h :=
    (Nat.card_eq_fintype_card (α := E)).symm.trans (GaloisField.card 2 h (by omega))
  have hfrE : Module.finrank F E = h := by
    have h1 := Module.card_eq_pow_finrank (K := F) (V := E)
    rw [hcardE, ZMod.card] at h1
    exact Nat.pow_right_injective (by omega : 2 ≤ 2) h1.symm
  let eBasis : Module.Basis (Fin h) F E := Module.finBasisOfFinrankEq F E hfrE
  let τ : E →ₗ[F] F := eBasis.coord ⟨0, by omega⟩
  have hτ_ne : τ ≠ 0 := by
    intro h0
    have : τ (eBasis ⟨0, by omega⟩) = 1 := by
      simp [τ, Module.Basis.coord_apply, eBasis.repr_self]
    rw [h0] at this
    simp at this
  let pair : E →ₗ[F] (E →ₗ[F] F) :=
    { toFun := fun u =>
        { toFun := fun c => τ (c * u)
          map_add' := fun c1 c2 => by rw [add_mul, map_add]
          map_smul' := fun a c => by simp [smul_mul_assoc, map_smul] }
      map_add' := fun u1 u2 => by ext c; simp [mul_add, map_add]
      map_smul' := fun a u => by ext c; simp [map_smul] }
  have hpair_inj : Function.Injective pair := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    by_contra hu0
    have hex : ∃ a : E, τ a ≠ 0 := by
      by_contra hall; push Not at hall; exact hτ_ne (LinearMap.ext hall)
    obtain ⟨a, ha⟩ := hex
    have h0 : pair u (a * u⁻¹) = 0 := by rw [hu]; rfl
    simp only [pair, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc, inv_mul_cancel₀ hu0, mul_one] at h0
    exact ha h0
  have hpair_surj : Function.Surjective pair := by
    have hfr : Module.finrank F E = Module.finrank F (E →ₗ[F] F) := by
      rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hpair_inj
  let pairEquiv : E ≃ₗ[F] (E →ₗ[F] F) := LinearEquiv.ofBijective pair ⟨hpair_inj, hpair_surj⟩
  let toDual (w : K) : E →ₗ[F] F :=
    { toFun := fun c => bit (c • w)
      map_add' := fun c1 c2 => by rw [add_smul, map_add]
      map_smul' := fun a c => by
        have : (a • c) • w = a • (c • w) := smul_assoc a c w
        simp [this, map_smul] }
  let Ψ : K →ₗ[E] E :=
    { toFun := fun w => pairEquiv.symm (toDual w)
      map_add' := fun w1 w2 => by
        apply pairEquiv.injective
        rw [map_add, pairEquiv.apply_symm_apply, pairEquiv.apply_symm_apply,
          pairEquiv.apply_symm_apply]
        ext c
        simp [toDual, smul_add, map_add]
      map_smul' := fun a w => by
        apply pairEquiv.injective
        rw [pairEquiv.apply_symm_apply]
        ext c
        simp only [RingHom.id_apply]
        have h1 : pairEquiv (a • pairEquiv.symm (toDual w)) c =
            τ (c * (a * pairEquiv.symm (toDual w))) := rfl
        have h2 : pairEquiv (pairEquiv.symm (toDual w)) (c * a) =
            τ ((c * a) * pairEquiv.symm (toDual w)) := rfl
        rw [h1, ← mul_assoc, ← h2, pairEquiv.apply_symm_apply]
        simp [toDual, mul_smul] }
  have hspec : ∀ (c : E) (w : K), bit (c • w) = τ (c * Ψ w) := by
    intro c w
    have h1 : pairEquiv (Ψ w) = toDual w := pairEquiv.apply_symm_apply (toDual w)
    have h2 := congrArg (fun f : E →ₗ[F] F => f c) h1
    exact h2.symm
  have hΨ_ne : Ψ ≠ 0 := by
    intro h0
    apply hbit
    ext w
    have := hspec 1 w
    rw [one_smul, h0] at this
    simpa using this
  exact ⟨eBasis, τ, Ψ, hΨ_ne, hspec⟩

private theorem main_proof (h m g : ℕ) (hh : 2 ≤ h) (hm : 0 < m) (hmg : m ≤ g * (g + 1) / 2)
    (K : Type) [Field K] [Algebra (ZMod 2) K] [Algebra (GaloisField 2 h) K]
    [IsScalarTower (ZMod 2) (GaloisField 2 h) K]
    [FiniteDimensional (GaloisField 2 h) K] [Fintype K]
    (hfrK : Module.finrank (GaloisField 2 h) K = m)
    (basis : Module.Basis (Fin (h * m)) (ZMod 2) K)
    (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) :
    let n := h * m + 1
    let point : Fin n → K := Fin.cases 0 basis
    let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
    ∃ (T : Fin (g * h) → Fin n → Fin n → Bool) (label : Fin (g * h) ≃ Fin g × Fin h),
      fits n n (g * h) T (g * h * ((h + 1) / 2)) ∧
      ∀ z : K, z ≠ 0 → ∃ S : Finset (Fin (g * h)), S.card ≤ 2 * h ∧
        (S.image (fun i => (label i).1)).card ≤ 2 ∧
        fits n n 1 (fun _ x y => xor (mult z x y)
          (((S.filter (fun i => T i x y)).card % 2) == 1)) ((h * m - h + 1) / 2) := by
  classical
  let F := ZMod 2
  let E := GaloisField 2 h
  let k := h * m
  let n := k + 1
  let point : Fin n → K := Fin.cases 0 basis
  let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
  obtain ⟨d, hd_span⟩ := exists_spanning_directions h m g hh hm hmg K hfrK
  obtain ⟨eBasis, τ, Ψ, hΨ_ne, hbit_eq⟩ := lift_bit_to_E h hh K bit hbit
  let label : Fin (g * h) ≃ Fin g × Fin h := finProdFinEquiv.symm
  let T : Fin (g * h) → Fin n → Fin n → Bool := fun i x y =>
    decide (τ (eBasis (label i).2 * Ψ (d (label i).1 * point x) * Ψ (d (label i).1 * point y)) ≠ 0)
  refine ⟨T, label, ?_, ?_⟩
  · apply fits_of_rank_le (r := h)
    intro j
    let a := (label j).1
    let b := (label j).2
    refine ⟨fun t x => eBasis.repr (Ψ (d a * point x)) t,
            fun t y => τ (eBasis b * eBasis t * Ψ (d a * point y)), fun x y => ?_⟩
    simp only [T, b2z_decide_ne_zero]
    have hexp : Ψ (d a * point x) = ∑ t : Fin h, eBasis.repr (Ψ (d a * point x)) t • eBasis t :=
      (eBasis.sum_repr (Ψ (d a * point x))).symm
    conv_lhs => rw [hexp]
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hsmul : eBasis b * (eBasis.repr (Ψ (d a * point x)) t • eBasis t) * Ψ (d a * point y) =
        eBasis.repr (Ψ (d a * point x)) t • (eBasis b * eBasis t * Ψ (d a * point y)) := by
      rw [mul_smul_comm, smul_mul_assoc]
    rw [hsmul, map_smul, smul_eq_mul]
  · intro z hz
    have hpair_ex : ∃ a1 a2 : Fin g, Ψ (z⁻¹ * (d a1 * d a2)) ≠ 0 := by
      by_contra hall
      push Not at hall
      have hker : ∀ w : K, Ψ (z⁻¹ * w) = 0 := by
        intro w
        have hw : w ∈ Submodule.span E (Set.range fun p : Fin g × Fin g => d p.1 * d p.2) := by
          rw [hd_span]; trivial
        induction hw using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨⟨a1, a2⟩, rfl⟩ := hu
          exact hall a1 a2
        | zero => simp
        | add u1 u2 _ _ ih1 ih2 => rw [mul_add, map_add, ih1, ih2, add_zero]
        | smul c u _ ih => rw [mul_smul_comm, map_smul, ih, smul_zero]
      apply hΨ_ne
      ext w
      have := hker (z * w)
      simpa [← mul_assoc, inv_mul_cancel₀ hz] using this
    obtain ⟨a1, a2, ha12⟩ := hpair_ex
    have hcoeff_sum : ∀ (a : Fin g) (c : E) (x y : Fin n),
        let Sa : Finset (Fin (g * h)) :=
          Finset.univ.filter (fun i => (label i).1 = a ∧ eBasis.repr c (label i).2 = 1)
        ∑ i ∈ Sa, b2z (T i x y) = τ (c * Ψ (d a * point x) * Ψ (d a * point y)) := by
      intro a c x y Sa
      have hbij : ∑ i ∈ Sa, b2z (T i x y) =
          ∑ b : Fin h, (eBasis.repr c b) * τ (eBasis b * Ψ (d a * point x) * Ψ (d a * point y)) := by
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun b : Fin h => eBasis.repr c b = 1)))]
        · refine Finset.sum_nbij (fun i => (label i).2) ?_ ?_ ?_ ?_
          · intro i hi
            rw [Finset.mem_filter] at hi ⊢
            exact ⟨Finset.mem_univ _, hi.2.2⟩
          · intro i1 hi1 i2 hi2 heq
            apply label.injective
            apply Prod.ext
            · exact (Finset.mem_filter.1 hi1).2.1.trans (Finset.mem_filter.1 hi2).2.1.symm
            · exact heq
          · intro b hb
            refine ⟨label.symm (a, b), ?_, by simp⟩
            refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
            simp [(Finset.mem_filter.1 hb).2]
          · intro i hi
            have h1 := (Finset.mem_filter.1 hi).2.1
            have h2 := (Finset.mem_filter.1 hi).2.2
            simp only [T, b2z_decide_ne_zero, h1, h2, one_mul]
        · intro b _ hb
          rw [Finset.mem_filter] at hb
          have hb0 : eBasis.repr c b = 0 := by
            rcases zmod2_cases (eBasis.repr c b) with h0 | h1
            · exact h0
            · exact False.elim (hb ⟨Finset.mem_univ _, h1⟩)
          simp [hb0]
      rw [hbij]
      have hc : c = ∑ b : Fin h, eBasis.repr c b • eBasis b := (eBasis.sum_repr c).symm
      conv_rhs => rw [hc]
      rw [Finset.sum_mul, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hsmul : (eBasis.repr c b • eBasis b) * Ψ (d a * point x) * Ψ (d a * point y) =
          eBasis.repr c b • (eBasis b * Ψ (d a * point x) * Ψ (d a * point y)) := by
        rw [smul_mul_assoc, smul_mul_assoc]
      rw [hsmul, map_smul, smul_eq_mul]
    have hfinish : ∀ (S : Finset (Fin (g * h))) (v : K) (hv0 : v ≠ 0)
        (B : K →ₗ[F] (K →ₗ[F] F)),
        S.card ≤ 2 * h → (S.image (fun i => (label i).1)).card ≤ 2 →
        (∀ x y : Fin n,
          b2z (xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)) =
            B (point x) (point y)) →
        (∀ (c : E) (y : K), B (c • v) y = 0) →
        ∃ S' : Finset (Fin (g * h)), S'.card ≤ 2 * h ∧
          (S'.image (fun i => (label i).1)).card ≤ 2 ∧
          fits n n 1 (fun _ x y => xor (mult z x y)
            (((S'.filter (fun i => T i x y)).card % 2) == 1)) ((h * m - h + 1) / 2) := by
      intro S v hv0 B hScard hSimg hBeq hBzero
      refine ⟨S, hScard, hSimg, ?_⟩
      have hfrK_F : Module.finrank F K = k := Module.finrank_eq_card_basis basis |>.trans (Fintype.card_fin k)
      let lineMap : E →ₗ[F] K :=
        { toFun := fun c => c • v
          map_add' := fun c1 c2 => add_smul c1 c2 v
          map_smul' := fun a c => smul_assoc a c v }
      have hline_inj : Function.Injective lineMap := by
        rw [injective_iff_map_eq_zero]
        intro c hc
        rcases smul_eq_zero.1 hc with h | h
        · exact h
        · exact False.elim (hv0 h)
      let L : Submodule F K := LinearMap.range lineMap
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      letI : Fintype E := Fintype.ofFinite E
      have hcardE : Fintype.card E = 2 ^ h :=
        (Nat.card_eq_fintype_card (α := E)).symm.trans (GaloisField.card 2 h (by omega))
      have hfrE : Module.finrank F E = h := by
        have h1 := Module.card_eq_pow_finrank (K := F) (V := E)
        rw [hcardE, ZMod.card] at h1
        exact Nat.pow_right_injective (by omega : 2 ≤ 2) h1.symm
      have hLfr : Module.finrank F L = h := by
        rw [← hfrE]
        exact (LinearEquiv.ofInjective lineMap hline_inj).finrank_eq.symm
      have hLle : L ≤ LinearMap.ker B := by
        rintro _ ⟨c, rfl⟩
        rw [LinearMap.mem_ker]
        ext y
        exact hBzero c y
      let Q := K ⧸ L
      have hQfr : Module.finrank F Q = k - h := by
        have hq := Submodule.finrank_quotient_add_finrank L
        rw [hLfr, hfrK_F] at hq
        change Module.finrank F Q + h = k at hq
        omega
      let qBasis : Module.Basis (Fin (k - h)) F Q := Module.finBasisOfFinrankEq F Q hQfr
      let Bq : Q →ₗ[F] (K →ₗ[F] F) := Submodule.liftQ L B hLle
      have hfits := fits_of_rank_le (n := n) (m := n) (q := 1) (r := k - h)
        (fun _ x y => xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1))
        (fun _ =>
          ⟨fun t x => qBasis.repr (Submodule.Quotient.mk (point x)) t,
           fun t y => Bq (qBasis t) (point y),
           fun x y => by
             rw [hBeq x y]
             have hlift : B (point x) (point y) = Bq (Submodule.Quotient.mk (point x)) (point y) := rfl
             rw [hlift]
             have hexp : Submodule.Quotient.mk (p := L) (point x) =
                 ∑ t : Fin (k - h), qBasis.repr (Submodule.Quotient.mk (point x)) t • qBasis t :=
               (qBasis.sum_repr _).symm
             conv_lhs => rw [hexp]
             rw [map_sum, LinearMap.sum_apply]
             refine Finset.sum_congr rfl fun t _ => ?_
             rw [map_smul, LinearMap.smul_apply, smul_eq_mul]⟩)
      simpa only [one_mul, k] using hfits
    have hS_eval : ∀ (S : Finset (Fin (g * h))) (x y : Fin n),
        b2z (xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)) =
          bit (z * point x * point y) + ∑ i ∈ S, b2z (T i x y) := by
      intro S x y
      rw [b2z_xor, b2z_mod2]
      congr 1
      · exact b2z_decide_ne_zero (bit (z * point x * point y))
      · have hsum : ∑ i ∈ S, b2z (T i x y) = ∑ i ∈ S.filter (fun i => T i x y), (1 : ZMod 2) := by
          rw [← Finset.sum_filter_add_sum_filter_not S (fun i => T i x y)]
          have h1 : ∑ i ∈ S.filter (fun i => T i x y), b2z (T i x y) =
              ∑ i ∈ S.filter (fun i => T i x y), (1 : ZMod 2) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            simp [(Finset.mem_filter.1 hi).2, b2z]
          have h2 : ∑ i ∈ S.filter (fun i => ¬T i x y = true), b2z (T i x y) = 0 := by
            refine Finset.sum_eq_zero fun i hi => ?_
            have hf : T i x y = false := Bool.eq_false_iff.2 (Finset.mem_filter.1 hi).2
            simp [hf, b2z]
          rw [h1, h2, add_zero]
        rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hSa_card : ∀ (a : Fin g) (c : E),
        (Finset.univ.filter (fun i : Fin (g * h) => (label i).1 = a ∧ eBasis.repr c (label i).2 = 1)).card ≤ h := by
      intro a c
      let Sa := Finset.univ.filter (fun i : Fin (g * h) => (label i).1 = a ∧ eBasis.repr c (label i).2 = 1)
      let f : { i // i ∈ Sa } → Fin h := fun ⟨i, _⟩ => (label i).2
      have hf_inj : Function.Injective f := by
        rintro ⟨i1, hi1⟩ ⟨i2, hi2⟩ heq
        apply Subtype.ext
        apply label.injective
        exact Prod.ext ((Finset.mem_filter.1 hi1).2.1.trans (Finset.mem_filter.1 hi2).2.1.symm) heq
      have hc := Fintype.card_le_of_injective f hf_inj
      rw [Fintype.card_coe, Fintype.card_fin] at hc
      exact hc
    by_cases h11 : Ψ (z⁻¹ * (d a1 * d a1)) ≠ 0
    · let c1 : E := (Ψ (z⁻¹ * (d a1 * d a1)))⁻¹
      let S : Finset (Fin (g * h)) :=
        Finset.univ.filter (fun i => (label i).1 = a1 ∧ eBasis.repr c1 (label i).2 = 1)
      let v : K := z⁻¹ * d a1
      have hv0 : v ≠ 0 := by
        intro hv
        apply h11
        have : z⁻¹ * (d a1 * d a1) = v * d a1 := by simp [v, mul_assoc]
        rw [this, hv, zero_mul, map_zero]
      let B : K →ₗ[F] (K →ₗ[F] F) :=
        { toFun := fun x =>
            { toFun := fun y => bit (z * x * y) + τ (c1 * Ψ (d a1 * x) * Ψ (d a1 * y))
              map_add' := fun y1 y2 => by simp [mul_add, map_add]; ring
              map_smul' := fun r y => by
                have hsmul1 : z * x * (r • y) = r • (z * x * y) := by rw [mul_smul_comm]
                have hsmul2 : d a1 * (r • y) = r • (d a1 * y) := by rw [mul_smul_comm]
                have hsmul3 : Ψ (r • (d a1 * y)) = r • Ψ (d a1 * y) := by
                  have : r • (d a1 * y) = (algebraMap F E r) • (d a1 * y) := by
                    rw [algebraMap_smul]
                  rw [this, map_smul, algebraMap_smul]
                simp only [RingHom.id_apply, hsmul1, hsmul2, hsmul3, mul_smul_comm, map_smul, smul_add] }
          map_add' := fun x1 x2 => by ext y; simp [mul_add, add_mul, map_add]; ring
          map_smul' := fun r x => by
            ext y
            have hsmul1 : z * (r • x) * y = r • (z * x * y) := by rw [mul_smul_comm, smul_mul_assoc]
            have hsmul2 : d a1 * (r • x) = r • (d a1 * x) := by rw [mul_smul_comm]
            have hsmul3 : Ψ (r • (d a1 * x)) = r • Ψ (d a1 * x) := by
              have : r • (d a1 * x) = (algebraMap F E r) • (d a1 * x) := by
                rw [algebraMap_smul]
              rw [this, map_smul, algebraMap_smul]
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
              hsmul1, hsmul2, hsmul3, mul_smul_comm, smul_mul_assoc, map_smul, smul_add] }
      have hSc : S.card ≤ 2 * h := by
        have h1 : S.card ≤ h := hSa_card a1 c1
        omega
      apply hfinish S v hv0 B hSc
      · have hsub : S.image (fun i => (label i).1) ⊆ {a1} := by
          intro a ha
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
          exact Finset.mem_singleton.2 (Finset.mem_filter.1 hi).2.1
        exact (Finset.card_le_card hsub).trans (by simp)
      · intro x y
        rw [hS_eval S x y, hcoeff_sum a1 c1 x y]
        rfl
      · intro c y
        show bit (z * (c • v) * y) + τ (c1 * Ψ (d a1 * (c • v)) * Ψ (d a1 * y)) = 0
        have h1 : z * (c • v) * y = c • (d a1 * y) := by
          simp only [v]
          rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
        have h2 : Ψ (d a1 * (c • v)) = c * Ψ (z⁻¹ * (d a1 * d a1)) := by
          have : d a1 * (c • v) = c • (z⁻¹ * (d a1 * d a1)) := by
            rw [mul_smul_comm]; congr 1; simp only [v]; ring
          rw [this, map_smul, smul_eq_mul]
        rw [h1, hbit_eq c (d a1 * y), h2]
        have hcancel : c1 * (c * Ψ (z⁻¹ * (d a1 * d a1))) * Ψ (d a1 * y) = c * Ψ (d a1 * y) := by
          calc c1 * (c * Ψ (z⁻¹ * (d a1 * d a1))) * Ψ (d a1 * y)
              = (c1 * Ψ (z⁻¹ * (d a1 * d a1))) * (c * Ψ (d a1 * y)) := by ring
            _ = 1 * (c * Ψ (d a1 * y)) := by rw [inv_mul_cancel₀ h11]
            _ = c * Ψ (d a1 * y) := one_mul _
        rw [hcancel]
        have h2z : ∀ t : ZMod 2, t + t = 0 := by decide
        exact h2z _
    · push Not at h11
      by_cases h22 : Ψ (z⁻¹ * (d a2 * d a2)) ≠ 0
      · let c2 : E := (Ψ (z⁻¹ * (d a2 * d a2)))⁻¹
        let S : Finset (Fin (g * h)) :=
          Finset.univ.filter (fun i => (label i).1 = a2 ∧ eBasis.repr c2 (label i).2 = 1)
        let v : K := z⁻¹ * d a2
        have hv0 : v ≠ 0 := by
          intro hv
          apply h22
          have : z⁻¹ * (d a2 * d a2) = v * d a2 := by simp [v, mul_assoc]
          rw [this, hv, zero_mul, map_zero]
        let B : K →ₗ[F] (K →ₗ[F] F) :=
          { toFun := fun x =>
              { toFun := fun y => bit (z * x * y) + τ (c2 * Ψ (d a2 * x) * Ψ (d a2 * y))
                map_add' := fun y1 y2 => by simp [mul_add, map_add]; ring
                map_smul' := fun r y => by
                  have hsmul1 : z * x * (r • y) = r • (z * x * y) := by rw [mul_smul_comm]
                  have hsmul2 : d a2 * (r • y) = r • (d a2 * y) := by rw [mul_smul_comm]
                  have hsmul3 : Ψ (r • (d a2 * y)) = r • Ψ (d a2 * y) := by
                    have : r • (d a2 * y) = (algebraMap F E r) • (d a2 * y) := by
                      rw [algebraMap_smul]
                    rw [this, map_smul, algebraMap_smul]
                  simp only [RingHom.id_apply, hsmul1, hsmul2, hsmul3, mul_smul_comm, map_smul, smul_add] }
            map_add' := fun x1 x2 => by ext y; simp [mul_add, add_mul, map_add]; ring
            map_smul' := fun r x => by
              ext y
              have hsmul1 : z * (r • x) * y = r • (z * x * y) := by rw [mul_smul_comm, smul_mul_assoc]
              have hsmul2 : d a2 * (r • x) = r • (d a2 * x) := by rw [mul_smul_comm]
              have hsmul3 : Ψ (r • (d a2 * x)) = r • Ψ (d a2 * x) := by
                have : r • (d a2 * x) = (algebraMap F E r) • (d a2 * x) := by
                  rw [algebraMap_smul]
                rw [this, map_smul, algebraMap_smul]
              simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
                hsmul1, hsmul2, hsmul3, mul_smul_comm, smul_mul_assoc, map_smul, smul_add] }
        have hSc : S.card ≤ 2 * h := by
          have h1 : S.card ≤ h := hSa_card a2 c2
          omega
        apply hfinish S v hv0 B hSc
        · have hsub : S.image (fun i => (label i).1) ⊆ {a2} := by
            intro a ha
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
            exact Finset.mem_singleton.2 (Finset.mem_filter.1 hi).2.1
          exact (Finset.card_le_card hsub).trans (by simp)
        · intro x y
          rw [hS_eval S x y, hcoeff_sum a2 c2 x y]
          rfl
        · intro c y
          show bit (z * (c • v) * y) + τ (c2 * Ψ (d a2 * (c • v)) * Ψ (d a2 * y)) = 0
          have h1 : z * (c • v) * y = c • (d a2 * y) := by
            simp only [v]
            rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
          have h2 : Ψ (d a2 * (c • v)) = c * Ψ (z⁻¹ * (d a2 * d a2)) := by
            have : d a2 * (c • v) = c • (z⁻¹ * (d a2 * d a2)) := by
              rw [mul_smul_comm]; congr 1; simp only [v]; ring
            rw [this, map_smul, smul_eq_mul]
          rw [h1, hbit_eq c (d a2 * y), h2]
          have hcancel : c2 * (c * Ψ (z⁻¹ * (d a2 * d a2))) * Ψ (d a2 * y) = c * Ψ (d a2 * y) := by
            calc c2 * (c * Ψ (z⁻¹ * (d a2 * d a2))) * Ψ (d a2 * y)
                = (c2 * Ψ (z⁻¹ * (d a2 * d a2))) * (c * Ψ (d a2 * y)) := by ring
              _ = 1 * (c * Ψ (d a2 * y)) := by rw [inv_mul_cancel₀ h22]
              _ = c * Ψ (d a2 * y) := one_mul _
          rw [hcancel]
          have h2z : ∀ t : ZMod 2, t + t = 0 := by decide
          exact h2z _
      · push Not at h22
        have hne12 : a1 ≠ a2 := fun heq => ha12 (heq ▸ h11)
        let α : E := Ψ (z⁻¹ * (d a1 * d a2))
        have hα0 : α ≠ 0 := ha12
        let c0 : E := α⁻¹
        let S1 : Finset (Fin (g * h)) :=
          Finset.univ.filter (fun i => (label i).1 = a1 ∧ eBasis.repr c0 (label i).2 = 1)
        let S2 : Finset (Fin (g * h)) :=
          Finset.univ.filter (fun i => (label i).1 = a2 ∧ eBasis.repr c0 (label i).2 = 1)
        let S : Finset (Fin (g * h)) := S1 ∪ S2
        have hdisj : Disjoint S1 S2 := by
          rw [Finset.disjoint_left]
          intro i hi1 hi2
          exact hne12 ((Finset.mem_filter.1 hi1).2.1.symm.trans (Finset.mem_filter.1 hi2).2.1)
        let v : K := z⁻¹ * (d a1 + d a2)
        have hv0 : v ≠ 0 := by
          intro hv
          apply hα0
          have hprod : d a1 * v = z⁻¹ * (d a1 * d a1) + z⁻¹ * (d a1 * d a2) := by
            simp only [v]; ring
          have h0 : Ψ (d a1 * v) = 0 := by rw [hv, mul_zero, map_zero]
          rw [hprod, map_add, h11, zero_add] at h0
          exact h0
        let B : K →ₗ[F] (K →ₗ[F] F) :=
          { toFun := fun x =>
              { toFun := fun y =>
                  bit (z * x * y) +
                  (τ (c0 * Ψ (d a1 * x) * Ψ (d a1 * y)) + τ (c0 * Ψ (d a2 * x) * Ψ (d a2 * y)))
                map_add' := fun y1 y2 => by simp [mul_add, map_add]; ring
                map_smul' := fun r y => by
                  have hsmul0 : z * x * (r • y) = r • (z * x * y) := by rw [mul_smul_comm]
                  have hsmul1 : Ψ (d a1 * (r • y)) = r • Ψ (d a1 * y) := by
                    rw [mul_smul_comm]
                    have : r • (d a1 * y) = (algebraMap F E r) • (d a1 * y) := by rw [algebraMap_smul]
                    rw [this, map_smul, algebraMap_smul]
                  have hsmul2 : Ψ (d a2 * (r • y)) = r • Ψ (d a2 * y) := by
                    rw [mul_smul_comm]
                    have : r • (d a2 * y) = (algebraMap F E r) • (d a2 * y) := by rw [algebraMap_smul]
                    rw [this, map_smul, algebraMap_smul]
                  rw [hsmul0, hsmul1, hsmul2]
                  simp only [RingHom.id_apply, mul_smul_comm, map_smul, smul_add] }
            map_add' := fun x1 x2 => by ext y; simp [mul_add, add_mul, map_add]; ring
            map_smul' := fun r x => by
              ext y
              have hsmul0 : z * (r • x) * y = r • (z * x * y) := by rw [mul_smul_comm, smul_mul_assoc]
              have hsmul1 : Ψ (d a1 * (r • x)) = r • Ψ (d a1 * x) := by
                rw [mul_smul_comm]
                have : r • (d a1 * x) = (algebraMap F E r) • (d a1 * x) := by rw [algebraMap_smul]
                rw [this, map_smul, algebraMap_smul]
              have hsmul2 : Ψ (d a2 * (r • x)) = r • Ψ (d a2 * x) := by
                rw [mul_smul_comm]
                have : r • (d a2 * x) = (algebraMap F E r) • (d a2 * x) := by rw [algebraMap_smul]
                rw [this, map_smul, algebraMap_smul]
              change bit (z * (r • x) * y) +
                (τ (c0 * Ψ (d a1 * (r • x)) * Ψ (d a1 * y)) +
                 τ (c0 * Ψ (d a2 * (r • x)) * Ψ (d a2 * y))) =
                r • (bit (z * x * y) +
                  (τ (c0 * Ψ (d a1 * x) * Ψ (d a1 * y)) +
                   τ (c0 * Ψ (d a2 * x) * Ψ (d a2 * y))))
              rw [hsmul0, hsmul1, hsmul2]
              simp only [mul_smul_comm, smul_mul_assoc, map_smul, smul_add] }
        have hSc : S.card ≤ 2 * h := by
          have hu := Finset.card_union_le S1 S2
          have h1 : S1.card ≤ h := hSa_card a1 c0
          have h2 : S2.card ≤ h := hSa_card a2 c0
          change (S1 ∪ S2).card ≤ 2 * h
          omega
        apply hfinish S v hv0 B hSc
        · have hsub : S.image (fun i => (label i).1) ⊆ {a1, a2} := by
            intro a ha
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
            rcases Finset.mem_union.1 hi with h1 | h2
            · exact Finset.mem_insert.2 (Or.inl (Finset.mem_filter.1 h1).2.1)
            · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 (Finset.mem_filter.1 h2).2.1))
          exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
        · intro x y
          rw [hS_eval S x y, Finset.sum_union hdisj, hcoeff_sum a1 c0 x y, hcoeff_sum a2 c0 x y]
          rfl
        · intro c y
          show bit (z * (c • v) * y) +
            (τ (c0 * Ψ (d a1 * (c • v)) * Ψ (d a1 * y)) +
             τ (c0 * Ψ (d a2 * (c • v)) * Ψ (d a2 * y))) = 0
          have h1 : z * (c • v) * y = c • ((d a1 + d a2) * y) := by
            simp only [v]
            rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
          have h2 : Ψ (d a1 * (c • v)) = c * α := by
            have : d a1 * (c • v) = c • (z⁻¹ * (d a1 * d a1) + z⁻¹ * (d a1 * d a2)) := by
              rw [mul_smul_comm]; congr 1; simp only [v]; ring
            rw [this, map_smul, map_add, h11, zero_add, smul_eq_mul]
          have h3 : Ψ (d a2 * (c • v)) = c * α := by
            have : d a2 * (c • v) = c • (z⁻¹ * (d a1 * d a2) + z⁻¹ * (d a2 * d a2)) := by
              rw [mul_smul_comm]; congr 1; simp only [v]; ring
            rw [this, map_smul, map_add, h22, add_zero, smul_eq_mul]
          rw [h1, hbit_eq c ((d a1 + d a2) * y), h2, h3]
          have hc1 : c0 * (c * α) * Ψ (d a1 * y) = c * Ψ (d a1 * y) := by
            calc c0 * (c * α) * Ψ (d a1 * y) = (c0 * α) * (c * Ψ (d a1 * y)) := by ring
              _ = 1 * (c * Ψ (d a1 * y)) := by rw [inv_mul_cancel₀ hα0]
              _ = c * Ψ (d a1 * y) := one_mul _
          have hc2 : c0 * (c * α) * Ψ (d a2 * y) = c * Ψ (d a2 * y) := by
            calc c0 * (c * α) * Ψ (d a2 * y) = (c0 * α) * (c * Ψ (d a2 * y)) := by ring
              _ = 1 * (c * Ψ (d a2 * y)) := by rw [inv_mul_cancel₀ hα0]
              _ = c * Ψ (d a2 * y) := one_mul _
          have hsum : τ (c * Ψ (d a1 * y)) + τ (c * Ψ (d a2 * y)) = τ (c * Ψ ((d a1 + d a2) * y)) := by
            rw [← map_add, ← mul_add, ← map_add, ← add_mul]
          rw [hc1, hc2, hsum]
          have h2z : ∀ t : ZMod 2, t + t = 0 := by decide
          exact h2z _

end PEqualNP.Outside.L_meta_29767

theorem PEqualNP.Outside.L_meta_29767 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

∀ (h m g : ℕ), 2 ≤ h → 0 < m → m ≤ g*(g+1)/2 →
  let F := ZMod 2
  let E := GaloisField 2 h
  let k := h*m
  let n := k+1
  ∀ (K : Type) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
      [FiniteDimensional E K] [Fintype K], Module.finrank E K = m →
    ∀ (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
      let point : Fin n → K := Fin.cases 0 basis
      let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
      ∃ (T : Fin (g*h) → Fin n → Fin n → Bool) (label : Fin (g*h) ≃ Fin g × Fin h),
        fits n n (g*h) T (g*h*((h+1)/2)) ∧
        ∀ z : K, z ≠ 0 → ∃ S : Finset (Fin (g*h)), S.card ≤ 2*h ∧
          (S.image (fun i => (label i).1)).card ≤ 2 ∧
          fits n n 1 (fun _ x y => xor (mult z x y)
            (((S.filter (fun i => T i x y)).card % 2) == 1)) ((k-h+1)/2)) := by
  intro nonlinear depths fits h m g hh hm hmg F E k n K _ _ _ _ _ _ hfrK basis bit hbit point mult
  exact PEqualNP.Outside.L_meta_29767.main_proof h m g hh hm hmg K hfrK basis bit hbit
