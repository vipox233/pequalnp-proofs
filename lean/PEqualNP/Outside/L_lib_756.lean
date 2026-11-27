import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_756_aux

open PEqualNP.CircuitLowerBounds

private def oneHot (p : ℕ) (x : Fin p) : List Bool :=
  List.ofFn (fun h : Fin p => decide (h = x))

private def isOr (g : Gate) : Prop :=
  g.op = GateOp.or ∧ g.inputs.length ≤ 2

private def isNot (g : Gate) : Prop :=
  g.op = GateOp.not ∧ g.inputs.length ≤ 1

private def hits (p q : ℕ) (A : Fin p → Fin q → Bool) (E : Circuit) : Prop :=
  ∀ y : Fin q, ∃ w : ℕ, ∀ x : Fin p, (E.wires (oneHot p x)).getD w false = A x y

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, stepW]; omega

private lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_length C.gates x

private lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl stepW w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepW w g) (by simp [stepW]; omega)]
    exact List.getD_append _ _ _ _ hk

private lemma wires_getD_input (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < x.length) :
    (C.wires x).getD k false = x.getD k false :=
  foldl_getD_lt C.gates x k hk

private lemma wires_getD_gate (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (x.length + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i =>
        if i < x.length + k then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    simp [List.take_append_getElem, List.take_append_drop]
  unfold Circuit.wires
  change (C.gates.foldl stepW x).getD (x.length + k) false = _
  let pref := (C.gates.take k).foldl stepW x
  have hpref_len : pref.length = x.length + k := by
    simp [pref, foldl_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hW_eq : C.gates.foldl stepW x = (C.gates.drop (k + 1)).foldl stepW (stepW pref C.gates[k]) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append]
    rfl
  have hstep_len : (stepW pref C.gates[k]).length = x.length + k + 1 := by
    simp [stepW, hpref_len]
  have hlt : x.length + k < (stepW pref C.gates[k]).length := by omega
  have hW_k : (C.gates.foldl stepW x).getD (x.length + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i => pref.getD i false) := by
    rw [hW_eq, foldl_getD_lt _ _ _ hlt]
    simp [stepW, List.getD_append_right _ _ _ _ (Nat.le_of_eq hpref_len), hpref_len]
  rw [hW_k]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  change pref.getD i false = if i < x.length + k then (C.gates.foldl stepW x).getD i false else false
  by_cases hi : i < x.length + k
  · rw [if_pos hi, hW_eq]
    rw [foldl_getD_lt (C.gates.drop (k + 1)) (stepW pref C.gates[k]) i (by omega)]
    rw [stepW, List.getD_append _ _ _ _ (by omega)]
  · rw [if_neg hi, List.getD_eq_default _ _ (by omega)]

private lemma getD_ofFn {p : ℕ} (f : Fin p → Bool) (k : ℕ) (hk : k < p) :
    (List.ofFn f).getD k false = f ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]

private lemma oneHot_getD (p : ℕ) (x : Fin p) (k : ℕ) :
    (oneHot p x).getD k false = decide (k = x.val) := by
  by_cases hk : k < p
  · unfold oneHot
    rw [getD_ofFn _ k hk]
    simp [Fin.ext_iff]
  · rw [List.getD_eq_default _ _ (by simp [oneHot]; omega)]
    have hne : k ≠ x.val := by omega
    simp [hne]

private lemma oneHot_length (p : ℕ) (x : Fin p) : (oneHot p x).length = p := by
  simp [oneHot]

private lemma or_circuit_linear (p : ℕ) (E : Circuit) (hor : ∀ g ∈ E.gates, isOr g)
    (v : Fin p → Bool) (w : ℕ) :
    (E.wires (List.ofFn v)).getD w false =
      decide (∃ x : Fin p, v x = true ∧ (E.wires (oneHot p x)).getD w false = true) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwp : w < p
    · rw [wires_getD_input E _ w (by simp [hwp]), getD_ofFn _ w hwp]
      have hrhs : ∀ x : Fin p, (E.wires (oneHot p x)).getD w false = decide (w = x.val) := fun x => by
        rw [wires_getD_input E _ w (by simp [oneHot_length, hwp]), oneHot_getD]
      simp only [hrhs, decide_eq_true_eq]
      cases hv : v ⟨w, hwp⟩
      · simp only [Bool.false_eq, decide_eq_false_iff_not, not_exists, not_and]
        intro x hx heq
        have : x = ⟨w, hwp⟩ := Fin.ext heq.symm
        subst this; simp [hv] at hx
      · simp only [Bool.true_eq, decide_eq_true_eq]
        exact ⟨⟨w, hwp⟩, hv, rfl⟩
    · by_cases hwN : w < p + E.gates.length
      · have hk : w - p < E.gates.length := by omega
        have hwk : p + (w - p) = w := by omega
        have h1 := wires_getD_gate E (List.ofFn v) (w - p) hk
        simp only [List.length_ofFn, hwk] at h1
        rw [h1]
        have hop : (E.gates[w - p]).op = GateOp.or := (hor _ (List.getElem_mem hk)).1
        rw [hop, GateOp.eval]
        have hstep : ∀ x : Fin p, (E.wires (oneHot p x)).getD w false =
            ((E.gates[w - p]).inputs.map fun i =>
              if i < w then (E.wires (oneHot p x)).getD i false else false).any id := fun x => by
          have hx := wires_getD_gate E (oneHot p x) (w - p) hk
          simp only [oneHot_length, hwk, hop, GateOp.eval] at hx
          exact hx
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, List.mem_map, id_eq, decide_eq_true_eq, hstep]
        constructor
        · rintro ⟨_, ⟨i, hi, heq⟩, rfl⟩
          by_cases hil : i < w
          · rw [if_pos hil, ih i hil, decide_eq_true_eq] at heq
            obtain ⟨x, hvx, hxi⟩ := heq
            exact ⟨x, hvx, true, ⟨i, hi, by rw [if_pos hil]; exact hxi⟩, rfl⟩
          · rw [if_neg hil] at heq; cases heq
        · rintro ⟨x, hvx, _, ⟨i, hi, heq⟩, rfl⟩
          by_cases hil : i < w
          · rw [if_pos hil] at heq
            refine ⟨true, ⟨i, hi, ?_⟩, rfl⟩
            rw [if_pos hil, ih i hil, decide_eq_true_eq]
            exact ⟨x, hvx, heq⟩
          · rw [if_neg hil] at heq; cases heq
      · rw [List.getD_eq_default _ _ (by rw [wires_length, List.length_ofFn]; omega)]
        symm
        simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro x _
        rw [List.getD_eq_default _ _ (by rw [wires_length, oneHot_length]; omega)]
        exact Bool.false_ne_true

private def dagEdge (p : ℕ) (E : Circuit) (a b : Fin (p + E.gates.length)) : Bool :=
  if h : p ≤ b.val then
    decide (a.val < b.val ∧ a.val ∈ (E.gates[b.val - p]'(by omega)).inputs)
  else false

private def dagReach (p : ℕ) (E : Circuit) (a b : Fin (p + E.gates.length)) : Prop :=
  Relation.ReflTransGen (fun u v => dagEdge p E u v = true) a b

private lemma dagEdge_lt {p : ℕ} {E : Circuit} {a b : Fin (p + E.gates.length)}
    (h : dagEdge p E a b = true) : a.val < b.val := by
  unfold dagEdge at h
  split_ifs at h with hp
  exact (decide_eq_true_eq.mp h).1

private lemma dagReach_le {p : ℕ} {E : Circuit} {a b : Fin (p + E.gates.length)}
    (h : dagReach p E a b) : a.val ≤ b.val := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans ih (Nat.le_of_lt (dagEdge_lt hstep))

private lemma wires_iff_dagReach (p : ℕ) (E : Circuit) (hor : ∀ g ∈ E.gates, isOr g)
    (x : Fin p) (b : Fin (p + E.gates.length)) :
    (E.wires (oneHot p x)).getD b.val false = true ↔
      dagReach p E ⟨x.val, by omega⟩ b := by
  induction hb : b.val using Nat.strong_induction_on generalizing b with
  | ind n ih =>
    by_cases hnp : n < p
    · have h1 : (E.wires (oneHot p x)).getD n false = decide (n = x.val) := by
        rw [wires_getD_input E _ n (by rw [oneHot_length]; omega), oneHot_getD]
      rw [h1, decide_eq_true_eq]
      constructor
      · intro heq
        have hb_eq : b = ⟨x.val, by omega⟩ := Fin.ext (hb.trans heq)
        rw [hb_eq]; exact Relation.ReflTransGen.refl
      · intro hr
        rcases Relation.ReflTransGen.cases_tail hr with rfl | ⟨c, _, hedge⟩
        · exact hb.symm
        · unfold dagEdge at hedge
          rw [dif_neg (by omega)] at hedge
          cases hedge
    · have hk : b.val - p < E.gates.length := by omega
      have hbk : p + (b.val - p) = n := by omega
      have h1 := wires_getD_gate E (oneHot p x) (b.val - p) hk
      simp only [oneHot_length, hbk] at h1
      have hop : (E.gates[b.val - p]).op = GateOp.or := (hor _ (List.getElem_mem hk)).1
      rw [h1, hop, GateOp.eval]
      simp only [List.any_eq_true, List.mem_map, id_eq]
      constructor
      · rintro ⟨_, ⟨i, hi, heq⟩, rfl⟩
        by_cases hil : i < n
        · rw [if_pos hil] at heq
          have hr := (ih i (by omega) ⟨i, by omega⟩ rfl).mp heq
          refine Relation.ReflTransGen.tail hr ?_
          unfold dagEdge
          rw [dif_pos (by omega), decide_eq_true_eq]
          exact ⟨by dsimp only; omega, hi⟩
        · rw [if_neg hil] at heq; cases heq
      · intro hr
        rcases Relation.ReflTransGen.cases_tail hr with heq | ⟨c, hrc, hedge⟩
        · have : b.val = x.val := congrArg Fin.val heq
          omega
        · unfold dagEdge at hedge
          rw [dif_pos (by omega), decide_eq_true_eq] at hedge
          have hc := (ih c.val (by omega) c rfl).mpr hrc
          refine ⟨true, ⟨c.val, hedge.2, ?_⟩, rfl⟩
          rw [if_pos (by omega : c.val < n)]
          exact hc

private lemma dagEdge_inDeg_le (p : ℕ) (E : Circuit) (hor : ∀ g ∈ E.gates, isOr g)
    (b : Fin (p + E.gates.length)) :
    (Finset.univ.filter (fun a : Fin (p + E.gates.length) => dagEdge p E a b = true)).card ≤
      if p ≤ b.val then 2 else 0 := by
  split_ifs with hbp
  · have hk : b.val - p < E.gates.length := by omega
    have hlen : (E.gates[b.val - p]).inputs.length ≤ 2 := (hor _ (List.getElem_mem hk)).2
    have hsub : (Finset.univ.filter (fun a : Fin (p + E.gates.length) => dagEdge p E a b = true)).image Fin.val ⊆
        (E.gates[b.val - p]).inputs.toFinset := by
      intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, dagEdge, dif_pos hbp, decide_eq_true_eq] at ha
      exact List.mem_toFinset.mpr ha.2
    calc (Finset.univ.filter (fun a : Fin (p + E.gates.length) => dagEdge p E a b = true)).card
        = ((Finset.univ.filter (fun a : Fin (p + E.gates.length) => dagEdge p E a b = true)).image Fin.val).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (E.gates[b.val - p]).inputs.toFinset.card := Finset.card_le_card hsub
      _ ≤ (E.gates[b.val - p]).inputs.length := List.toFinset_card_le _
      _ ≤ 2 := hlen
  · have hemp : Finset.univ.filter (fun a : Fin (p + E.gates.length) => dagEdge p E a b = true) = ∅ := by
      ext a
      simp [dagEdge, dif_neg hbp]
    rw [hemp, Finset.card_empty]

private def orFold (base : ℕ) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], acc)
  | w :: rest =>
    let g : Gate := ⟨GateOp.or, [acc, w]⟩
    let res := orFold (base + 1) base rest
    (g :: res.1, res.2)

private lemma orFold_len (base acc : ℕ) (ws : List ℕ) :
    (orFold base acc ws).1.length = ws.length := by
  induction ws generalizing base acc with
  | nil => rfl
  | cons w rest ih => simp [orFold, ih]

private lemma orFold_isOr (base acc : ℕ) (ws : List ℕ) :
    ∀ g ∈ (orFold base acc ws).1, isOr g := by
  induction ws generalizing base acc with
  | nil => intro g hg; cases hg
  | cons w rest ih =>
    intro g hg
    simp only [orFold, List.mem_cons] at hg
    rcases hg with rfl | hrest
    · exact ⟨rfl, by simp⟩
    · exact ih _ _ g hrest

private lemma orFold_out_lt (base acc : ℕ) (ws : List ℕ) (hacc : acc < base) :
    (orFold base acc ws).2 < base + ws.length := by
  induction ws generalizing base acc with
  | nil => simpa [orFold] using hacc
  | cons w rest ih =>
    simp only [orFold, List.length_cons]
    have h := ih (base + 1) base (by omega)
    omega

private lemma orFold_eval (W : List Bool) (acc : ℕ) (ws : List ℕ)
    (hacc : acc < W.length) (hws : ∀ u ∈ ws, u < W.length) :
    (((orFold W.length acc ws).1).foldl stepW W).getD (orFold W.length acc ws).2 false =
      (W.getD acc false || ws.any (fun u => W.getD u false)) := by
  induction ws generalizing W acc with
  | nil => simp [orFold]
  | cons w rest ih =>
    simp only [orFold, List.foldl_cons, List.any_cons]
    let g : Gate := ⟨GateOp.or, [acc, w]⟩
    let W' := stepW W g
    have hW'_len : W'.length = W.length + 1 := by simp [W', stepW]
    have hlt_w : w < W.length := hws w List.mem_cons_self
    have hW'_acc : W'.getD W.length false = (W.getD acc false || W.getD w false) := by
      simp [W', stepW, g, GateOp.eval, List.getD_append_right _ _ _ _ (le_refl W.length)]
    have hW'_lt : ∀ u < W.length, W'.getD u false = W.getD u false := fun u hu => by
      exact List.getD_append _ _ _ _ hu
    have ih' := ih W' W.length (by omega) (fun u hu => by
      have := hws u (List.mem_cons_of_mem _ hu); omega)
    rw [hW'_len] at ih'
    rw [ih', hW'_acc]
    have hany : rest.any (fun u => W'.getD u false) = rest.any (fun u => W.getD u false) := by
      have haux : ∀ l : List ℕ, (∀ u ∈ l, u < W.length) →
          l.any (fun u => W'.getD u false) = l.any (fun u => W.getD u false) := by
        intro l hl
        induction l with
        | nil => rfl
        | cons a t iht =>
          simp only [List.any_cons, hW'_lt a (hl a List.mem_cons_self),
            iht (fun u hu => hl u (List.mem_cons_of_mem _ hu))]
      exact haux rest (fun u hu => hws u (List.mem_cons_of_mem _ hu))
    rw [hany, Bool.or_assoc]

private theorem or_transpose (p q : ℕ) (R : Fin p → Fin q → Bool) (E : Circuit)
    (hhits : hits p q R E) (hor : ∀ g ∈ E.gates, isOr g) :
    ∃ D : Circuit, hits q p (fun y x => R x y) D ∧ (∀ g ∈ D.gates, isOr g) ∧
      D.size + ((Finset.univ : Finset (Fin p)).filter (fun u => ∃ v, R u v = true)).card ≤
        E.size + ((Finset.univ : Finset (Fin q)).filter (fun v => ∃ u, R u v = true)).card := by
  classical
  let N := p + E.gates.length
  let NZRow : Finset (Fin p) := Finset.univ.filter (fun x => ∃ y, R x y = true)
  let NZCol : Finset (Fin q) := Finset.univ.filter (fun y => ∃ x, R x y = true)
  choose wOf hwOf using hhits
  have hwOf_lt : ∀ y ∈ NZCol, wOf y < N := by
    intro y hy
    simp only [NZCol, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨x, hxy⟩ := hy
    have hev := hwOf y x
    rw [hxy] at hev
    by_contra hge
    have hdef : (E.wires (oneHot p x)).getD (wOf y) false = false :=
      List.getD_eq_default _ _ (by rw [wires_length, oneHot_length]; omega)
    rw [hdef] at hev
    exact Bool.false_ne_true hev
  let Act : Finset (Fin N) := Finset.univ.filter (fun a =>
    (∃ x : Fin p, dagReach p E ⟨x.val, by omega⟩ a) ∧
    (∃ y : Fin q, ∃ hy : y ∈ NZCol, dagReach p E a ⟨wOf y, hwOf_lt y hy⟩))

  have hbuild : ∀ k ≤ N,
      ∃ (gs : List Gate) (wireOf : Fin N → ℕ),
        (∀ g ∈ gs, isOr g) ∧
        (∀ a ∈ Act, N - k ≤ a.val →
          wireOf a < q + gs.length ∧
          ∀ y : Fin q, ((gs.foldl stepW (oneHot q y)).getD (wireOf a) false = true ↔
            ∃ hy : y ∈ NZCol, dagReach p E a ⟨wOf y, hwOf_lt y hy⟩)) ∧
        gs.length + (Act.filter (fun a => N - k ≤ a.val)).card =
          ∑ a ∈ Act.filter (fun a => N - k ≤ a.val),
            ((NZCol.filter (fun y => wOf y = a.val)).card +
             (Act.filter (fun b => dagEdge p E a b = true)).card) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun _ => 0, ?_, ?_, ?_⟩
      · intro _ h; cases h
      · intro a _ hge; omega
      · have hemp : Act.filter (fun a : Fin N => N - 0 ≤ a.val) = ∅ := by
          ext a; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]; intro _; omega
        rw [hemp]; simp
    | succ k' ih =>
      intro hk
      obtain ⟨gs, wireOf, hgs_or, hgs_spec, hgs_len⟩ := ih (by omega)
      let a0 : Fin N := ⟨N - 1 - k', by omega⟩
      by_cases ha0 : a0 ∈ Act
      ·
        let sinks : List (Fin q) := (NZCol.filter (fun y => wOf y = a0.val)).toList
        let outs : List (Fin N) := (Act.filter (fun b => dagEdge p E a0 b = true)).toList
        let kids : List ℕ := sinks.map Fin.val ++ outs.map wireOf
        have hkids_len : kids.length =
            (NZCol.filter (fun y => wOf y = a0.val)).card +
            (Act.filter (fun b => dagEdge p E a0 b = true)).card := by
          simp [kids, sinks, outs]
        have hkids_ne : kids ≠ [] := by
          intro hemp
          have h0 : kids.length = 0 := by rw [hemp]; rfl
          rw [hkids_len] at h0
          have ha0_spec := (Finset.mem_filter.mp ha0).2
          obtain ⟨y, hy, hr⟩ := ha0_spec.2
          rcases Relation.ReflTransGen.cases_head hr with heq | ⟨b, hedge, hrb⟩
          · have hwy : wOf y = a0.val := (congrArg Fin.val heq).symm
            have hmem : y ∈ NZCol.filter (fun y => wOf y = a0.val) := Finset.mem_filter.mpr ⟨hy, hwy⟩
            have hpos := Finset.card_pos.mpr ⟨y, hmem⟩
            omega
          · have hb_act : b ∈ Act := by
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_, ⟨y, hy, hrb⟩⟩
              obtain ⟨x, hrx⟩ := ha0_spec.1
              exact ⟨x, Relation.ReflTransGen.tail hrx hedge⟩
            have hmem : b ∈ Act.filter (fun b => dagEdge p E a0 b = true) :=
              Finset.mem_filter.mpr ⟨hb_act, hedge⟩
            have hpos := Finset.card_pos.mpr ⟨b, hmem⟩
            omega
        cases hkids_cons : kids with
        | nil => exact absurd hkids_cons hkids_ne
        | cons w0 rest =>
          have hkids_lt : ∀ u ∈ kids, u < q + gs.length := by
            intro u hu
            simp only [kids, List.mem_append, List.mem_map] at hu
            rcases hu with ⟨y, _, rfl⟩ | ⟨b, hb, rfl⟩
            · omega
            · have hb' : b ∈ Act.filter (fun b => dagEdge p E a0 b = true) :=
                Finset.mem_toList.mp hb
              rw [Finset.mem_filter] at hb'
              have hlt := dagEdge_lt hb'.2
              exact (hgs_spec b hb'.1 (by dsimp [a0] at hlt; omega)).1
          have hw0_lt : w0 < q + gs.length := hkids_lt w0 (by rw [hkids_cons]; simp)
          have hrest_lt : ∀ u ∈ rest, u < q + gs.length := fun u hu =>
            hkids_lt u (by rw [hkids_cons]; exact List.mem_cons_of_mem _ hu)
          let res := orFold (q + gs.length) w0 rest
          let gs' := gs ++ res.1
          let wireOf' : Fin N → ℕ := fun a => if a = a0 then res.2 else wireOf a
          have hres_len : res.1.length + 1 = kids.length := by
            have := congrArg List.length hkids_cons
            simp only [List.length_cons] at this
            rw [orFold_len]
            omega
          refine ⟨gs', wireOf', ?_, ?_, ?_⟩
          · intro g hg
            rw [List.mem_append] at hg
            rcases hg with h1 | h2
            · exact hgs_or g h1
            · exact orFold_isOr _ _ _ g h2
          · intro a ha hge
            by_cases ha_eq : a = a0
            · subst ha_eq
              simp only [wireOf', ite_true]
              refine ⟨?_, ?_⟩
              · have := orFold_out_lt (q + gs.length) w0 rest hw0_lt
                simp only [gs', List.length_append, res, orFold_len]; omega
              · intro y
                let W := gs.foldl stepW (oneHot q y)
                have hW_len : W.length = q + gs.length := by
                  simp [W, foldl_length, oneHot_length]
                have hev : (gs'.foldl stepW (oneHot q y)).getD res.2 false =
                    (W.getD w0 false || rest.any (fun u => W.getD u false)) := by
                  simp only [gs', List.foldl_append, res]
                  have := orFold_eval W w0 rest (by omega) (fun u hu => by
                    have := hrest_lt u hu; omega)
                  simpa only [hW_len] using this
                rw [hev]
                have hany_kids : (W.getD w0 false || rest.any (fun u => W.getD u false)) =
                    kids.any (fun u => W.getD u false) := by
                  rw [hkids_cons, List.any_cons]
                rw [hany_kids, List.any_eq_true]
                constructor
                · rintro ⟨u, hu, hWu⟩
                  simp only [kids, List.mem_append, List.mem_map] at hu
                  rcases hu with ⟨y', hy', rfl⟩ | ⟨b, hb, rfl⟩
                  · have hy'_mem := Finset.mem_filter.mp (Finset.mem_toList.mp hy')
                    have hW_y' : W.getD y'.val false = decide (y'.val = y.val) := by
                      rw [foldl_getD_lt _ _ _ (by rw [oneHot_length]; exact y'.isLt), oneHot_getD]
                    rw [hW_y', decide_eq_true_eq] at hWu
                    have hy_eq : y' = y := Fin.ext hWu
                    subst hy_eq
                    refine ⟨hy'_mem.1, ?_⟩
                    have ha0_eq : a0 = ⟨wOf y', hwOf_lt y' hy'_mem.1⟩ := Fin.ext hy'_mem.2.symm
                    exact ha0_eq ▸ Relation.ReflTransGen.refl
                  · have hb_mem := Finset.mem_filter.mp (Finset.mem_toList.mp hb)
                    have hlt := dagEdge_lt hb_mem.2
                    obtain ⟨hy, hrb⟩ := ((hgs_spec b hb_mem.1 (by dsimp [a0] at hlt; omega)).2 y).mp hWu
                    exact ⟨hy, Relation.ReflTransGen.head hb_mem.2 hrb⟩
                · rintro ⟨hy, hr⟩
                  rcases Relation.ReflTransGen.cases_head hr with heq | ⟨b, hedge, hrb⟩
                  · have hwy : wOf y = a0.val := (congrArg Fin.val heq).symm
                    refine ⟨y.val, ?_, ?_⟩
                    · simp only [kids, List.mem_append, List.mem_map]
                      left
                      exact ⟨y, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hy, hwy⟩), rfl⟩
                    · rw [foldl_getD_lt _ _ _ (by rw [oneHot_length]; exact y.isLt), oneHot_getD]
                      simp
                  · have hb_act : b ∈ Act := by
                      rw [Finset.mem_filter]
                      refine ⟨Finset.mem_univ _, ?_, ⟨y, hy, hrb⟩⟩
                      obtain ⟨x, hrx⟩ := (Finset.mem_filter.mp ha0).2.1
                      exact ⟨x, Relation.ReflTransGen.tail hrx hedge⟩
                    have hlt := dagEdge_lt hedge
                    have hWb := ((hgs_spec b hb_act (by dsimp [a0] at hlt; omega)).2 y).mpr ⟨hy, hrb⟩
                    refine ⟨wireOf b, ?_, hWb⟩
                    simp only [kids, List.mem_append, List.mem_map]
                    right
                    exact ⟨b, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hb_act, hedge⟩), rfl⟩
            · simp only [wireOf', if_neg ha_eq]
              have hge' : N - k' ≤ a.val := by
                have hne : a.val ≠ N - 1 - k' := fun h => ha_eq (Fin.ext h)
                omega
              have hsp := hgs_spec a ha hge'
              refine ⟨by simp [gs']; omega, fun y => ?_⟩
              have hsame : (gs'.foldl stepW (oneHot q y)).getD (wireOf a) false =
                  (gs.foldl stepW (oneHot q y)).getD (wireOf a) false := by
                simp only [gs', List.foldl_append]
                apply foldl_getD_lt
                rw [foldl_length, oneHot_length]
                exact hsp.1
              rw [hsame]
              exact hsp.2 y
          · have hfilt : Act.filter (fun a => N - (k' + 1) ≤ a.val) =
                insert a0 (Act.filter (fun a => N - k' ≤ a.val)) := by
              ext a
              simp only [Finset.mem_filter, Finset.mem_insert]
              constructor
              · rintro ⟨ha, hle⟩
                by_cases heq : a.val = N - 1 - k'
                · exact Or.inl (Fin.ext heq)
                · exact Or.inr ⟨ha, by omega⟩
              · rintro (rfl | ⟨ha, hle⟩)
                · exact ⟨ha0, by dsimp [a0]; omega⟩
                · exact ⟨ha, by omega⟩
            have hnotmem : a0 ∉ Act.filter (fun a => N - k' ≤ a.val) := by
              simp only [Finset.mem_filter, not_and]; intro _; dsimp [a0]; omega
            rw [hfilt, Finset.card_insert_of_notMem hnotmem, Finset.sum_insert hnotmem]
            simp only [gs', List.length_append]
            omega
      ·
        have hfilt : Act.filter (fun a => N - (k' + 1) ≤ a.val) =
            Act.filter (fun a => N - k' ≤ a.val) := by
          ext a
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨ha, hle⟩
            have hne : a.val ≠ N - 1 - k' := fun heq => ha0 ((Fin.ext (by dsimp [a0]; exact heq) : a = a0) ▸ ha)
            exact ⟨ha, by omega⟩
          · rintro ⟨ha, hle⟩
            exact ⟨ha, by omega⟩
        refine ⟨gs, wireOf, hgs_or, ?_, ?_⟩
        · intro a ha hle
          have hne : a.val ≠ N - 1 - k' := fun heq => ha0 ((Fin.ext (by dsimp [a0]; exact heq) : a = a0) ▸ ha)
          exact hgs_spec a ha (by omega)
        · rw [hfilt]; exact hgs_len

  obtain ⟨gs, wireOf, hgs_or, hgs_spec, hgs_len⟩ := hbuild N le_rfl
  have hAct_all : Act.filter (fun a : Fin N => N - N ≤ a.val) = Act := by
    ext a; simp
  rw [hAct_all] at hgs_len
  let D : Circuit := ⟨gs, 0⟩
  refine ⟨D, ?_, hgs_or, ?_⟩
  ·
    intro x
    by_cases hx : x ∈ NZRow
    · have hx_act : (⟨x.val, by omega⟩ : Fin N) ∈ Act := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ⟨x, Relation.ReflTransGen.refl⟩, ?_⟩
        obtain ⟨y, hxy⟩ := (Finset.mem_filter.mp hx).2
        have hy : y ∈ NZCol := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxy⟩
        have hev := hwOf y x
        rw [hxy] at hev
        exact ⟨y, hy, (wires_iff_dagReach p E hor x ⟨wOf y, hwOf_lt y hy⟩).mp hev⟩
      refine ⟨wireOf ⟨x.val, by omega⟩, fun y => ?_⟩
      have hspec := (hgs_spec ⟨x.val, by omega⟩ hx_act (by omega)).2 y
      apply Bool.eq_iff_iff.mpr
      change ((gs.foldl stepW (oneHot q y)).getD (wireOf ⟨x.val, by omega⟩) false = true) ↔ R x y = true
      rw [hspec]
      constructor
      · rintro ⟨hy, hr⟩
        have h1 := (wires_iff_dagReach p E hor x ⟨wOf y, hwOf_lt y hy⟩).mpr hr
        rw [hwOf y x] at h1; exact h1
      · intro hxy
        have hy : y ∈ NZCol := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxy⟩
        have h1 : (E.wires (oneHot p x)).getD (wOf y) false = true := by rw [hwOf y x]; exact hxy
        exact ⟨hy, (wires_iff_dagReach p E hor x ⟨wOf y, hwOf_lt y hy⟩).mp h1⟩
    · refine ⟨q + gs.length, fun y => ?_⟩
      have hfalse : R x y = false := by
        cases hxy : R x y
        · rfl
        · exact False.elim (hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hxy⟩))
      dsimp only
      rw [hfalse]
      exact List.getD_eq_default _ _ (by rw [wires_length, oneHot_length])
  ·
    change gs.length + NZRow.card ≤ E.gates.length + NZCol.card
    let ActIn := Act.filter (fun a : Fin N => a.val < p)
    let ActG := Act.filter (fun a : Fin N => p ≤ a.val)
    have hAct_split : Act.card = ActIn.card + ActG.card := by
      have h := Finset.card_filter_add_card_filter_not (s := Act) (p := fun a : Fin N => a.val < p)
      have hge : Act.filter (fun a : Fin N => ¬a.val < p) = ActG := by
        ext a; simp [ActG, not_lt]
      rw [hge] at h; exact h.symm
    have hActIn_eq : ActIn.card = NZRow.card := by
      refine Finset.card_bij (fun a ha => ⟨a.val, (Finset.mem_filter.mp ha).2⟩) ?_ ?_ ?_
      · intro a ha
        have ha' := Finset.mem_filter.mp ha
        obtain ⟨y, hy, hr⟩ := (Finset.mem_filter.mp ha'.1).2.2
        have h1 := (wires_iff_dagReach p E hor ⟨a.val, ha'.2⟩ ⟨wOf y, hwOf_lt y hy⟩).mpr hr
        rw [hwOf y _] at h1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, h1⟩
      · intro a1 _ a2 _ heq
        exact Fin.ext (congrArg (Fin.val (n := p)) heq)
      · intro x hx
        obtain ⟨y, hxy⟩ := (Finset.mem_filter.mp hx).2
        have hy : y ∈ NZCol := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxy⟩
        have h1 : (E.wires (oneHot p x)).getD (wOf y) false = true := by rw [hwOf y x]; exact hxy
        have hr := (wires_iff_dagReach p E hor x ⟨wOf y, hwOf_lt y hy⟩).mp h1
        refine ⟨⟨x.val, by omega⟩, ?_, Fin.ext rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, Relation.ReflTransGen.refl⟩, ⟨y, hy, hr⟩⟩, x.isLt⟩
    have hActG_le : ActG.card ≤ E.gates.length := by
      let f : Fin N → ℕ := fun a => a.val - p
      have hinj : Set.InjOn f ↑ActG := by
        intro a1 ha1 a2 ha2 heq
        have h1 := (Finset.mem_filter.mp ha1).2
        have h2 := (Finset.mem_filter.mp ha2).2
        dsimp [f] at heq
        exact Fin.ext (by omega)
      have hsub : ActG.image f ⊆ Finset.range E.gates.length := by
        intro k hk
        rw [Finset.mem_image] at hk
        obtain ⟨a, ha, rfl⟩ := hk
        have := (Finset.mem_filter.mp ha).2
        rw [Finset.mem_range]; dsimp [f]; omega
      calc ActG.card = (ActG.image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range E.gates.length).card := Finset.card_le_card hsub
        _ = E.gates.length := Finset.card_range _

    have hsink_sum : ∑ a ∈ Act, (NZCol.filter (fun y => wOf y = a.val)).card = NZCol.card := by
      have hbi : NZCol = Act.biUnion (fun a => NZCol.filter (fun y => wOf y = a.val)) := by
        ext y
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · intro hy
          obtain ⟨x, hxy⟩ := (Finset.mem_filter.mp hy).2
          have h1 : (E.wires (oneHot p x)).getD (wOf y) false = true := by rw [hwOf y x]; exact hxy
          have hr := (wires_iff_dagReach p E hor x ⟨wOf y, hwOf_lt y hy⟩).mp h1
          have hw_act : (⟨wOf y, hwOf_lt y hy⟩ : Fin N) ∈ Act :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hr⟩, ⟨y, hy, Relation.ReflTransGen.refl⟩⟩
          exact ⟨⟨wOf y, hwOf_lt y hy⟩, hw_act, hy, rfl⟩
        · rintro ⟨_, _, hy, _⟩; exact hy
      have hdisj : Set.PairwiseDisjoint (Act : Set (Fin N)) (fun a => NZCol.filter (fun y => wOf y = a.val)) := by
        intro a1 _ a2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro y h1 h2
        have e1 := (Finset.mem_filter.mp h1).2
        have e2 := (Finset.mem_filter.mp h2).2
        exact hne (Fin.ext (e1.symm.trans e2))
      conv_rhs => rw [hbi]
      rw [Finset.card_biUnion hdisj]

    have hedge_sum : ∑ a ∈ Act, (Act.filter (fun b => dagEdge p E a b = true)).card ≤ 2 * ActG.card := by
      have hswap : ∑ a ∈ Act, (Act.filter (fun b => dagEdge p E a b = true)).card =
          ∑ b ∈ Act, (Act.filter (fun a => dagEdge p E a b = true)).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
      rw [hswap]
      calc ∑ b ∈ Act, (Act.filter (fun a => dagEdge p E a b = true)).card
          ≤ ∑ b ∈ Act, (Finset.univ.filter (fun a => dagEdge p E a b = true)).card :=
            Finset.sum_le_sum fun b _ => Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
        _ ≤ ∑ b ∈ Act, (if p ≤ b.val then 2 else 0) :=
            Finset.sum_le_sum fun b _ => dagEdge_inDeg_le p E hor b
        _ = 2 * ActG.card := by
            rw [← Finset.sum_filter]
            simp [ActG, mul_comm]
    rw [Finset.sum_add_distrib, hsink_sum] at hgs_len
    omega

private lemma forward_dir (n m : ℕ) (M : Fin n → Fin m → Bool) (b s : ℕ)
    (C : Circuit) (hhits : hits n m M C)
    (hgates : ∀ g ∈ C.gates, isOr g ∨ isNot g)
    (hsz : C.size ≤ s)
    (hb : C.gates.countP (fun g => @decide (isNot g) (Classical.propDecidable _)) ≤ b) :
    ∃ t : ℕ, t ≤ b ∧ ∃ (R : Fin (n + t) → Fin (m + t) → Bool) (z : Fin n → Fin t → Bool),
      (∀ i j : Fin t, j ≤ i → R (Fin.natAdd n i) (Fin.natAdd m j) = false) ∧
      (∀ (x : Fin n) (j : Fin t), z x j =
        !(R (Fin.castAdd t x) (Fin.natAdd m j) ||
          decide (∃ i : Fin t, i < j ∧ z x i = true ∧ R (Fin.natAdd n i) (Fin.natAdd m j) = true))) ∧
      (∀ (x : Fin n) (y : Fin m), M x y =
        (R (Fin.castAdd t x) (Fin.castAdd t y) ||
          decide (∃ i : Fin t, z x i = true ∧ R (Fin.natAdd n i) (Fin.castAdd t y) = true))) ∧
      ∃ D : Circuit,
        hits (m + t) (n + t) (fun y x => R x y) D ∧ (∀ g ∈ D.gates, isOr g) ∧
        D.size + ((Finset.univ : Finset (Fin (n + t))).filter (fun u => ∃ v, R u v = true)).card + t ≤
          s + ((Finset.univ : Finset (Fin (m + t))).filter (fun v => ∃ u, R u v = true)).card := by
  classical

  let isNotB (g : Gate) : Bool := decide (g.op = GateOp.not)
  have hisNot_iff : ∀ g ∈ C.gates, isNotB g = true ↔ isNot g := fun g hg => by
    simp only [isNotB, decide_eq_true_eq]
    constructor
    · intro hop
      rcases hgates g hg with hor | hnot
      · rw [hor.1] at hop; cases hop
      · exact hnot
    · intro hnot; exact hnot.1
  have hcount_eq : C.gates.countP isNotB =
      C.gates.countP (fun g => @decide (isNot g) (Classical.propDecidable _)) := by
    have haux : ∀ l : List Gate, (∀ g ∈ l, isNotB g = @decide (isNot g) (Classical.propDecidable _)) →
        l.countP isNotB = l.countP (fun g => @decide (isNot g) (Classical.propDecidable _)) := by
      intro l hl
      induction l with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.countP_cons, hl g List.mem_cons_self, ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
    apply haux C.gates
    intro g hg
    apply Bool.eq_iff_iff.mpr
    rw [hisNot_iff g hg]
    simp
  let notIdxs : List ℕ := (List.range C.gates.length).filter (fun k =>
    if h : k < C.gates.length then isNotB C.gates[k] else false)
  let orIdxs : List ℕ := (List.range C.gates.length).filter (fun k =>
    if h : k < C.gates.length then !isNotB C.gates[k] else false)
  let t := notIdxs.length

  have hfilter_len : ∀ (P : Gate → Bool) (l : List Gate),
      ((List.range l.length).filter (fun k => if h : k < l.length then P l[k] else false)).length =
        l.countP P := by
    intro P l
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton l g ih =>
      have hlen : (l ++ [g]).length = l.length + 1 := by simp
      have hrange : List.range (l ++ [g]).length = List.range l.length ++ [l.length] := by
        rw [hlen, List.range_succ]
      rw [hrange, List.filter_append, List.length_append, List.countP_append, List.countP_singleton]
      have h1 : (List.range l.length).filter (fun k => if h : k < (l ++ [g]).length then P (l ++ [g])[k] else false) =
          (List.range l.length).filter (fun k => if h : k < l.length then P l[k] else false) := by
        apply List.filter_congr
        intro k hk
        rw [List.mem_range] at hk
        rw [dif_pos (by omega), dif_pos hk, List.getElem_append_left hk]
      have h2 : ([l.length].filter (fun k => if h : k < (l ++ [g]).length then P (l ++ [g])[k] else false)).length =
          if P g then 1 else 0 := by
        simp only [List.filter_cons, List.filter_nil]
        rw [dif_pos (by omega), List.getElem_append_right (le_refl l.length)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        cases P g <;> simp
      rw [h1, ih, h2]
  have ht_eq : t = C.gates.countP isNotB := hfilter_len isNotB C.gates
  have ht_le_b : t ≤ b := by rw [ht_eq, hcount_eq]; exact hb
  have hor_len_eq : orIdxs.length = C.gates.countP (fun g => !isNotB g) :=
    hfilter_len (fun g => !isNotB g) C.gates
  have hsum_len : t + orIdxs.length = C.gates.length := by
    rw [ht_eq, hor_len_eq]
    have haux : ∀ l : List Gate, l.countP isNotB + l.countP (fun g => !isNotB g) = l.length := by
      intro l; induction l with
      | nil => simp
      | cons g gs ih => simp only [List.countP_cons, List.length_cons]; cases isNotB g <;> simp <;> omega
    exact haux C.gates

  have hnot_sorted : notIdxs.Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
  have hor_sorted : orIdxs.Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
  have hnot_lt : ∀ j : Fin t, notIdxs[j.val] < C.gates.length := fun j => by
    have hm := List.mem_filter.mp (List.getElem_mem j.isLt)
    exact List.mem_range.mp hm.1
  have hor_lt : ∀ r : Fin orIdxs.length, orIdxs[r.val] < C.gates.length := fun r => by
    have hm := List.mem_filter.mp (List.getElem_mem r.isLt)
    exact List.mem_range.mp hm.1
  have hnot_isNot : ∀ j : Fin t, isNot (C.gates[notIdxs[j.val]]'(hnot_lt j)) := fun j => by
    have hm := List.mem_filter.mp (List.getElem_mem j.isLt)
    have h1 := hm.2
    rw [dif_pos (hnot_lt j)] at h1
    exact (hisNot_iff _ (List.getElem_mem (hnot_lt j))).mp h1
  have hor_isOr : ∀ r : Fin orIdxs.length, isOr (C.gates[orIdxs[r.val]]'(hor_lt r)) := fun r => by
    have hm := List.mem_filter.mp (List.getElem_mem r.isLt)
    have h1 := hm.2
    rw [dif_pos (hor_lt r)] at h1
    have hnn : ¬isNot (C.gates[orIdxs[r.val]]'(hor_lt r)) := fun h => by
      have := (hisNot_iff _ (List.getElem_mem (hor_lt r))).mpr h
      simp [this] at h1
    rcases hgates _ (List.getElem_mem (hor_lt r)) with ho | hn
    · exact ho
    · exact absurd hn hnn
  have hnot_mono : ∀ i j : Fin t, i < j → notIdxs[i.val] < notIdxs[j.val] := fun i j hij =>
    List.pairwise_iff_getElem.mp hnot_sorted i.val j.val i.isLt j.isLt hij
  have hor_mono : ∀ r1 r2 : Fin orIdxs.length, r1 < r2 → orIdxs[r1.val] < orIdxs[r2.val] := fun r1 r2 hr =>
    List.pairwise_iff_getElem.mp hor_sorted r1.val r2.val r1.isLt r2.isLt hr

  let N_E := n + t + orIdxs.length
  let mapWire (u : ℕ) : ℕ :=
    if u < n then u
    else if h : u < n + C.gates.length then
      let k := u - n
      match notIdxs.idxOf? k with
      | some j => n + j
      | none =>
        match orIdxs.idxOf? k with
        | some r => n + t + r
        | none => N_E
    else N_E

  have hmap_in : ∀ u < n, mapWire u = u := fun u hu => by simp [mapWire, hu]
  have hmap_not : ∀ j : Fin t, mapWire (n + notIdxs[j.val]) = n + j.val := fun j => by
    have hlt := hnot_lt j
    have hnd : notIdxs.Nodup := hnot_sorted.imp ne_of_lt
    have hidx : notIdxs.idxOf? notIdxs[j.val] = some j.val := by
      rw [List.idxOf?_eq_some_iff]
      refine ⟨j.isLt, rfl, fun i hi => ?_⟩
      exact ne_of_lt (hnot_mono ⟨i, by omega⟩ j hi)
    simp [mapWire, show ¬(n + notIdxs[j.val] < n) by omega,
      show n + notIdxs[j.val] < n + C.gates.length by omega, hidx]
  have hmap_or : ∀ r : Fin orIdxs.length, mapWire (n + orIdxs[r.val]) = n + t + r.val := fun r => by
    have hlt := hor_lt r
    have hnot_mem : orIdxs[r.val] ∉ notIdxs := by
      intro hm
      have h1 := (List.mem_filter.mp hm).2
      have h2 := (List.mem_filter.mp (List.getElem_mem r.isLt)).2
      rw [dif_pos hlt] at h1 h2
      simp [h1] at h2
    have hnone : notIdxs.idxOf? orIdxs[r.val] = none := List.idxOf?_eq_none_iff.mpr hnot_mem
    have hidx : orIdxs.idxOf? orIdxs[r.val] = some r.val := by
      rw [List.idxOf?_eq_some_iff]
      refine ⟨r.isLt, rfl, fun i hi => ?_⟩
      exact ne_of_lt (hor_mono ⟨i, by omega⟩ r hi)
    simp [mapWire, show ¬(n + orIdxs[r.val] < n) by omega,
      show n + orIdxs[r.val] < n + C.gates.length by omega, hnone, hidx]

  let E_gates : List Gate := List.ofFn (fun r : Fin orIdxs.length =>
    let k := orIdxs[r.val]
    let g := C.gates[k]'(hor_lt r)
    ⟨GateOp.or, (g.inputs.filter (· < n + k)).map mapWire⟩)
  let E : Circuit := ⟨E_gates, 0⟩
  have hE_len : E.gates.length = orIdxs.length := by simp [E, E_gates]
  have hE_or : ∀ g ∈ E.gates, isOr g := by
    intro g hg
    simp only [E, E_gates, List.mem_ofFn] at hg
    obtain ⟨r, rfl⟩ := hg
    refine ⟨rfl, ?_⟩
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) (hor_isOr r).2

  have hmap_lt_or : ∀ (r : Fin orIdxs.length) (u : ℕ), u < n + orIdxs[r.val] → mapWire u < n + t + r.val := by
    intro r u hu
    by_cases hun : u < n
    · rw [hmap_in u hun]; omega
    · have huC : u < n + C.gates.length := by have := hor_lt r; omega
      have hk : u - n < C.gates.length := by omega
      by_cases hnot : isNotB (C.gates[u - n]'hk) = true
      · have hmem : u - n ∈ notIdxs := List.mem_filter.mpr ⟨List.mem_range.mpr hk, by rw [dif_pos hk]; exact hnot⟩
        obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
        have hueq : u = n + notIdxs[j] := by omega
        rw [hueq, hmap_not ⟨j, hj⟩]; omega
      · have hmem : u - n ∈ orIdxs := List.mem_filter.mpr ⟨List.mem_range.mpr hk, by
          rw [dif_pos hk]; cases hc : isNotB (C.gates[u - n]'hk) <;> simp_all⟩
        obtain ⟨r', hr', hget⟩ := List.mem_iff_getElem.mp hmem
        have hueq : u = n + orIdxs[r'] := by omega
        rw [hueq, hmap_or ⟨r', hr'⟩]
        have hrlt : r' < r.val := by
          by_contra hge
          push_neg at hge
          rcases Nat.eq_or_lt_of_le hge with heq | hgt
          · have hge2 : orIdxs[r'] = orIdxs[r.val] := by simp [heq]
            omega
          · have hlt_m := hor_mono r ⟨r', hr'⟩ hgt
            dsimp only at hlt_m
            omega
        dsimp only
        omega

  have hmap_causal : ∀ (j i : Fin t), j ≤ i → ∀ u : ℕ, u < n + notIdxs[j.val] →
      (E.wires (oneHot (n + t) (Fin.natAdd n i))).getD (mapWire u) false = false := by
    intro j i hji u
    induction u using Nat.strong_induction_on with
    | ind u ih =>
      intro hu
      by_cases hun : u < n
      · rw [hmap_in u hun, wires_getD_input E _ u (by rw [oneHot_length]; omega), oneHot_getD]
        simp [Fin.natAdd, show u ≠ n + i.val by omega]
      · have huC : u < n + C.gates.length := by have := hnot_lt j; omega
        have hk : u - n < C.gates.length := by omega
        by_cases hnot : isNotB (C.gates[u - n]'hk) = true
        · have hmem : u - n ∈ notIdxs := List.mem_filter.mpr ⟨List.mem_range.mpr hk, by rw [dif_pos hk]; exact hnot⟩
          obtain ⟨j', hj', hget⟩ := List.mem_iff_getElem.mp hmem
          have hueq : u = n + notIdxs[j'] := by omega
          rw [hueq, hmap_not ⟨j', hj'⟩, wires_getD_input E _ (n + j') (by rw [oneHot_length]; omega), oneHot_getD]
          have hj'lt : j' < j.val := by
            by_contra hge; push_neg at hge
            rcases Nat.eq_or_lt_of_le hge with heq | hgt
            · have hge2 : notIdxs[j'] = notIdxs[j.val] := by simp [heq]
              omega
            · have hlt_m := hnot_mono j ⟨j', hj'⟩ hgt
              dsimp only at hlt_m
              omega
          have hne_ni : n + j' ≠ n + i.val := by
            have := hji
            change j.val ≤ i.val at this
            omega
          simp only [Fin.natAdd, decide_eq_false_iff_not]
          exact hne_ni
        · have hmem : u - n ∈ orIdxs := List.mem_filter.mpr ⟨List.mem_range.mpr hk, by
            rw [dif_pos hk]; cases hc : isNotB (C.gates[u - n]'hk) <;> simp_all⟩
          obtain ⟨r, hr, hget⟩ := List.mem_iff_getElem.mp hmem
          have hueq : u = n + orIdxs[r] := by omega
          rw [hueq, hmap_or ⟨r, hr⟩]
          have hg := wires_getD_gate E (oneHot (n + t) (Fin.natAdd n i)) r (by rw [hE_len]; exact hr)
          simp only [oneHot_length] at hg
          rw [hg]
          have hEg : E.gates[r]'(by rw [hE_len]; exact hr) =
              ⟨GateOp.or, ((C.gates[orIdxs[r]]'(hor_lt ⟨r, hr⟩)).inputs.filter (· < n + orIdxs[r])).map mapWire⟩ := by
            simp [E, E_gates]
          rw [hEg, GateOp.eval]
          simp only [List.any_eq_false, List.mem_map, id_eq, Bool.not_eq_true]
          rintro _ ⟨w, hw, rfl⟩
          obtain ⟨u', hu', rfl⟩ := hw
          rw [List.mem_filter, decide_eq_true_eq] at hu'
          rw [if_pos (hmap_lt_or ⟨r, hr⟩ u' hu'.2)]
          exact ih u' (by omega) (by omega)

  let z : Fin n → Fin t → Bool := fun x j =>
    (C.wires (oneHot n x)).getD (n + notIdxs[j.val]) false
  choose wM hwM using hhits

  let notInWire (j : Fin t) : ℕ :=
    let k := notIdxs[j.val]
    match (C.gates[k]'(hnot_lt j)).inputs with
    | [] => N_E
    | u :: _ => if u < n + k then mapWire u else N_E
  let outWire (v : Fin (m + t)) : ℕ :=
    if hv : v.val < m then mapWire (wM ⟨v.val, hv⟩)
    else notInWire ⟨v.val - m, by omega⟩
  let R : Fin (n + t) → Fin (m + t) → Bool := fun u v =>
    (E.wires (oneHot (n + t) u)).getD (outWire v) false

  let vIn (x : Fin n) : Fin (n + t) → Bool := fun u =>
    if hu : u.val < n then decide (u.val = x.val)
    else z x ⟨u.val - n, by omega⟩
  have hsim : ∀ (x : Fin n) (u : ℕ),
      (E.wires (List.ofFn (vIn x))).getD (mapWire u) false =
        (C.wires (oneHot n x)).getD u false := by
    intro x u
    induction u using Nat.strong_induction_on with
    | ind u ih =>
      by_cases hun : u < n
      · rw [hmap_in u hun, wires_getD_input E _ u (by simp; omega),
          wires_getD_input C _ u (by rw [oneHot_length]; exact hun), oneHot_getD,
          getD_ofFn _ u (by omega)]
        simp [vIn, hun]
      · by_cases huC : u < n + C.gates.length
        · have hk : u - n < C.gates.length := by omega
          by_cases hnot : isNotB (C.gates[u - n]'hk) = true
          · have hmem : u - n ∈ notIdxs := List.mem_filter.mpr ⟨List.mem_range.mpr hk, by rw [dif_pos hk]; exact hnot⟩
            obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
            have hueq : u = n + notIdxs[j] := by omega
            rw [hueq, hmap_not ⟨j, hj⟩, wires_getD_input E _ (n + j) (by simp; omega),
              getD_ofFn _ (n + j) (by omega)]
            simp [vIn, show ¬(n + j < n) by omega, z]
          · have hmem : u - n ∈ orIdxs := List.mem_filter.mpr ⟨List.mem_range.mpr hk, by
              rw [dif_pos hk]; cases hc : isNotB (C.gates[u - n]'hk) <;> simp_all⟩
            obtain ⟨r, hr, hget⟩ := List.mem_iff_getElem.mp hmem
            have hueq : u = n + orIdxs[r] := by omega
            rw [hueq, hmap_or ⟨r, hr⟩]
            have hE_g := wires_getD_gate E (List.ofFn (vIn x)) r (by rw [hE_len]; exact hr)
            simp only [List.length_ofFn] at hE_g
            have hC_g := wires_getD_gate C (oneHot n x) orIdxs[r] (hor_lt ⟨r, hr⟩)
            simp only [oneHot_length] at hC_g
            rw [hE_g, hC_g]
            have hEg : E.gates[r]'(by rw [hE_len]; exact hr) =
                ⟨GateOp.or, ((C.gates[orIdxs[r]]'(hor_lt ⟨r, hr⟩)).inputs.filter (· < n + orIdxs[r])).map mapWire⟩ := by
              simp [E, E_gates]
            have hCop : (C.gates[orIdxs[r]]'(hor_lt ⟨r, hr⟩)).op = GateOp.or := (hor_isOr ⟨r, hr⟩).1
            rw [hEg, hCop, GateOp.eval, GateOp.eval]
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true, List.mem_map, id_eq]
            constructor
            · rintro ⟨_, ⟨w, hw, rfl⟩, htrue⟩
              obtain ⟨u', hu', rfl⟩ := hw
              rw [List.mem_filter, decide_eq_true_eq] at hu'
              rw [if_pos (hmap_lt_or ⟨r, hr⟩ u' hu'.2), ih u' (by omega)] at htrue
              exact ⟨true, ⟨u', hu'.1, by rw [if_pos hu'.2]; exact htrue⟩, rfl⟩
            · rintro ⟨_, ⟨u', hu', htrue⟩, rfl⟩
              by_cases hu'lt : u' < n + orIdxs[r]
              · rw [if_pos hu'lt] at htrue
                refine ⟨true, ⟨mapWire u', ⟨u', List.mem_filter.mpr ⟨hu', decide_eq_true hu'lt⟩, rfl⟩, ?_⟩, rfl⟩
                rw [if_pos (hmap_lt_or ⟨r, hr⟩ u' hu'lt), ih u' (by omega)]
                exact htrue
              · rw [if_neg hu'lt] at htrue; cases htrue
        · have hmN : mapWire u = N_E := by simp [mapWire, show ¬(u < n) by omega, huC]
          rw [hmN, List.getD_eq_default _ _ (by rw [wires_length, List.length_ofFn, hE_len]),
            List.getD_eq_default _ _ (by rw [wires_length, oneHot_length]; omega)]

  have hR_causal : ∀ i j : Fin t, j ≤ i → R (Fin.natAdd n i) (Fin.natAdd m j) = false := by
    intro i j hji
    have hnm : ¬(Fin.natAdd m j).val < m := by simp [Fin.natAdd]
    simp only [R, outWire, dif_neg hnm]
    have hsub : (Fin.natAdd m j).val - m = j.val := by simp [Fin.natAdd]
    have hfin : (⟨(Fin.natAdd m j).val - m, by omega⟩ : Fin t) = j := Fin.ext hsub
    rw [hfin]
    dsimp [notInWire]
    cases h : (C.gates[notIdxs[j.val]]'(hnot_lt j)).inputs with
    | nil =>
      dsimp only
      exact List.getD_eq_default _ _ (by rw [wires_length, oneHot_length, hE_len])
    | cons u _ =>
      dsimp only
      by_cases hult : u < n + notIdxs[j.val]
      · rw [if_pos hult]
        exact hmap_causal j i hji u hult
      · rw [if_neg hult]
        exact List.getD_eq_default _ _ (by rw [wires_length, oneHot_length, hE_len])

  have hz_rec : ∀ (x : Fin n) (j : Fin t), z x j =
      !(R (Fin.castAdd t x) (Fin.natAdd m j) ||
        decide (∃ i : Fin t, i < j ∧ z x i = true ∧ R (Fin.natAdd n i) (Fin.natAdd m j) = true)) := by
    intro x j
    have hlin := or_circuit_linear (n + t) E hE_or (vIn x) (outWire (Fin.natAdd m j))
    have hlhs_eq : (E.wires (List.ofFn (vIn x))).getD (outWire (Fin.natAdd m j)) false =
        (R (Fin.castAdd t x) (Fin.natAdd m j) ||
          decide (∃ i : Fin t, i < j ∧ z x i = true ∧ R (Fin.natAdd n i) (Fin.natAdd m j) = true)) := by
      rw [hlin]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.or_eq_true]
      constructor
      · rintro ⟨u, hvu, hEu⟩
        by_cases hun : u.val < n
        · simp only [vIn, dif_pos hun, decide_eq_true_eq] at hvu
          left
          have hueq : u = Fin.castAdd t x := Fin.ext hvu
          subst hueq; exact hEu
        · simp only [vIn, dif_neg hun] at hvu
          let i : Fin t := ⟨u.val - n, by omega⟩
          have hueq : u = Fin.natAdd n i := Fin.ext (by dsimp [i, Fin.natAdd]; omega)
          rw [hueq] at hEu
          have hilt : i < j := by
            by_contra hge
            have hfalse := hR_causal i j (Nat.le_of_not_lt hge)
            change (E.wires (oneHot (n + t) (Fin.natAdd n i))).getD (outWire (Fin.natAdd m j)) false = false at hfalse
            rw [hfalse] at hEu; exact Bool.false_ne_true hEu
          exact Or.inr ⟨i, hilt, hvu, hEu⟩
      · rintro (hxR | ⟨i, _, hzi, hiR⟩)
        · exact ⟨Fin.castAdd t x, by simp [vIn], hxR⟩
        · exact ⟨Fin.natAdd n i, by simp [vIn, Fin.natAdd, show ¬(n + i.val < n) by omega, hzi], hiR⟩
    rw [← hlhs_eq]
    have hCg := wires_getD_gate C (oneHot n x) notIdxs[j.val] (hnot_lt j)
    simp only [oneHot_length] at hCg
    have hop : (C.gates[notIdxs[j.val]]'(hnot_lt j)).op = GateOp.not := (hnot_isNot j).1
    dsimp [z]
    rw [hCg, hop, GateOp.eval]
    congr 1
    have hnm : ¬(Fin.natAdd m j).val < m := by simp [Fin.natAdd]
    simp only [outWire, dif_neg hnm]
    have hsub : (Fin.natAdd m j).val - m = j.val := by simp [Fin.natAdd]
    have hfin : (⟨(Fin.natAdd m j).val - m, by omega⟩ : Fin t) = j := Fin.ext hsub
    rw [hfin]
    dsimp [notInWire]
    cases h : (C.gates[notIdxs[j.val]]'(hnot_lt j)).inputs with
    | nil =>
      simp only [List.map_nil, List.headD_nil]
      exact (List.getD_eq_default _ _ (by rw [wires_length, List.length_ofFn, hE_len])).symm
    | cons u _ =>
      simp only [List.map_cons, List.headD_cons]
      by_cases hult : u < n + notIdxs[j.val]
      · rw [if_pos hult, if_pos hult, hsim x u]
      · rw [if_neg hult, if_neg hult]
        exact (List.getD_eq_default _ _ (by rw [wires_length, List.length_ofFn, hE_len])).symm

  have hM_rec : ∀ (x : Fin n) (y : Fin m), M x y =
      (R (Fin.castAdd t x) (Fin.castAdd t y) ||
        decide (∃ i : Fin t, z x i = true ∧ R (Fin.natAdd n i) (Fin.castAdd t y) = true)) := by
    intro x y
    have hlin := or_circuit_linear (n + t) E hE_or (vIn x) (outWire (Fin.castAdd t y))
    have hout_eq : outWire (Fin.castAdd t y) = mapWire (wM y) := by
      simp [outWire, Fin.castAdd]
    have hM1 : M x y = (E.wires (List.ofFn (vIn x))).getD (outWire (Fin.castAdd t y)) false := by
      rw [hout_eq, hsim x (wM y), hwM y x]
    rw [hM1, hlin]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    constructor
    · rintro ⟨u, hvu, hEu⟩
      by_cases hun : u.val < n
      · simp only [vIn, dif_pos hun, decide_eq_true_eq] at hvu
        left
        have hueq : u = Fin.castAdd t x := Fin.ext hvu
        subst hueq; exact hEu
      · simp only [vIn, dif_neg hun] at hvu
        let i : Fin t := ⟨u.val - n, by omega⟩
        have hueq : u = Fin.natAdd n i := Fin.ext (by dsimp [i, Fin.natAdd]; omega)
        rw [hueq] at hEu
        exact Or.inr ⟨i, hvu, hEu⟩
    · rintro (hxR | ⟨i, hzi, hiR⟩)
      · exact ⟨Fin.castAdd t x, by simp [vIn], hxR⟩
      · exact ⟨Fin.natAdd n i, by simp [vIn, Fin.natAdd, show ¬(n + i.val < n) by omega, hzi], hiR⟩

  have hE_hits : hits (n + t) (m + t) R E := fun v => ⟨outWire v, fun u => rfl⟩
  obtain ⟨D, hD_hits, hD_or, hD_budget⟩ := or_transpose (n + t) (m + t) R E hE_hits hE_or
  refine ⟨t, ht_le_b, R, z, hR_causal, hz_rec, hM_rec, D, hD_hits, hD_or, ?_⟩
  change E.gates.length = orIdxs.length at hE_len
  change C.gates.length ≤ s at hsz
  change D.gates.length + _ ≤ E.gates.length + _ at hD_budget
  change D.gates.length + _ + t ≤ s + _
  omega

private lemma backward_dir (n m : ℕ) (M : Fin n → Fin m → Bool) (b s : ℕ)
    (t : ℕ) (ht : t ≤ b)
    (R : Fin (n + t) → Fin (m + t) → Bool)
    (z : Fin n → Fin t → Bool)
    (hR_causal : ∀ i j : Fin t, j ≤ i → R (Fin.natAdd n i) (Fin.natAdd m j) = false)
    (hz_rec : ∀ (x : Fin n) (j : Fin t), z x j =
      !(R (Fin.castAdd t x) (Fin.natAdd m j) ||
        decide (∃ i : Fin t, i < j ∧ z x i = true ∧ R (Fin.natAdd n i) (Fin.natAdd m j) = true)))
    (hM_rec : ∀ (x : Fin n) (y : Fin m), M x y =
      (R (Fin.castAdd t x) (Fin.castAdd t y) ||
        decide (∃ i : Fin t, z x i = true ∧ R (Fin.natAdd n i) (Fin.castAdd t y) = true)))
    (D : Circuit)
    (hD_hits : hits (m + t) (n + t) (fun y x => R x y) D)
    (hD_or : ∀ g ∈ D.gates, isOr g)
    (hD_budget : D.size + ((Finset.univ : Finset (Fin (n + t))).filter (fun u => ∃ v, R u v = true)).card + t ≤
      s + ((Finset.univ : Finset (Fin (m + t))).filter (fun v => ∃ u, R u v = true)).card) :
    ∃ C : Circuit, hits n m M C ∧
      (∀ g ∈ C.gates, isOr g ∨ isNot g) ∧ C.size ≤ s ∧
      C.gates.countP (fun g => @decide (isNot g) (Classical.propDecidable _)) ≤ b := by
  classical

  obtain ⟨E, hE_hits, hE_or, hE_budget⟩ := or_transpose (m + t) (n + t) (fun y x => R x y) D hD_hits hD_or
  have hE_sz : E.size + t ≤ s := by
    change E.size + ((Finset.univ : Finset (Fin (m + t))).filter (fun y => ∃ x, R x y = true)).card ≤
      D.size + ((Finset.univ : Finset (Fin (n + t))).filter (fun x => ∃ y, R x y = true)).card at hE_budget
    omega
  choose wE hwE using hE_hits
  let N_E := n + t + E.gates.length

  let lvl (u : ℕ) : ℕ :=
    (Finset.univ.filter (fun i : Fin t =>
      (E.wires (oneHot (n + t) (Fin.natAdd n i))).getD u false = true)).sup (fun i => i.val + 1)
  have hlvl_le_t : ∀ u, lvl u ≤ t := fun u =>
    Finset.sup_le fun i _ => by omega
  have hlvl_zero_of_in : ∀ x : Fin n, lvl x.val = 0 := fun x => by
    apply Nat.eq_zero_of_le_zero
    refine Finset.sup_le fun i hi => ?_
    rw [Finset.mem_filter] at hi
    have h1 := hi.2
    rw [wires_getD_input E _ x.val (by rw [oneHot_length]; omega), oneHot_getD] at h1
    simp [Fin.natAdd, show x.val ≠ n + i.val by omega] at h1
  have hlvl_extra : ∀ j : Fin t, lvl (n + j.val) = j.val + 1 := fun j => by
    apply le_antisymm
    · refine Finset.sup_le fun i hi => ?_
      rw [Finset.mem_filter] at hi
      have h1 := hi.2
      rw [wires_getD_input E _ (n + j.val) (by rw [oneHot_length]; omega), oneHot_getD] at h1
      simp only [Fin.natAdd, decide_eq_true_eq] at h1
      omega
    · refine Finset.le_sup (f := fun i : Fin t => i.val + 1) ?_
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [wires_getD_input E _ (n + j.val) (by rw [oneHot_length]; omega), oneHot_getD]
      simp [Fin.natAdd]
  have hlvl_not_in : ∀ j : Fin t, lvl (wE (Fin.natAdd m j)) ≤ j.val := fun j => by
    refine Finset.sup_le fun i hi => ?_
    rw [Finset.mem_filter] at hi
    have h1 := hi.2
    rw [hwE (Fin.natAdd m j) (Fin.natAdd n i)] at h1
    dsimp only at h1
    by_contra hgt
    have hfalse := hR_causal i j (by omega)
    rw [hfalse] at h1; exact Bool.false_ne_true h1
  have hlvl_gate_mono : ∀ (k : Fin E.gates.length) (u : ℕ),
      u ∈ (E.gates[k.val]).inputs → u < n + t + k.val → lvl u ≤ lvl (n + t + k.val) := by
    intro k u hu hult
    refine Finset.sup_le fun i hi => ?_
    rw [Finset.mem_filter] at hi
    refine Finset.le_sup (f := fun i : Fin t => i.val + 1) ?_
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hg := wires_getD_gate E (oneHot (n + t) (Fin.natAdd n i)) k.val k.isLt
    simp only [oneHot_length, (hE_or _ (List.getElem_mem k.isLt)).1, GateOp.eval] at hg
    rw [hg, List.any_eq_true]
    exact ⟨true, List.mem_map.mpr ⟨u, hu, by rw [if_pos hult]; exact hi.2⟩, rfl⟩

  let orAt (lev : ℕ) : List (Fin E.gates.length ⊕ Fin t) :=
    ((List.finRange E.gates.length).filter (fun k => decide (lvl (n + t + k.val) = lev))).map Sum.inl
  let order : List (Fin E.gates.length ⊕ Fin t) :=
    ((List.finRange t).flatMap (fun j => orAt j.val ++ [Sum.inr j])) ++ orAt t
  have horder_nodup : order.Nodup := by
    have hparts_nd : ∀ lev, (orAt lev).Nodup := fun lev =>
      ((List.nodup_finRange _).filter _).map Sum.inl_injective
    have hdisj_or : ∀ l1 l2, l1 ≠ l2 → List.Disjoint (orAt l1) (orAt l2) := by
      intro l1 l2 hne x h1 h2
      simp only [orAt, List.mem_map, List.mem_filter, decide_eq_true_eq] at h1 h2
      obtain ⟨k1, ⟨_, e1⟩, rfl⟩ := h1
      obtain ⟨k2, ⟨_, e2⟩, heq⟩ := h2
      have hk := Sum.inl.inj heq
      subst hk; exact hne (e1.symm.trans e2)
    rw [List.nodup_append]
    refine ⟨?_, hparts_nd t, ?_⟩
    · rw [List.nodup_flatMap]
      refine ⟨fun j _ => ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hparts_nd j.val, List.nodup_singleton _, fun x hx y hy heq => ?_⟩
        subst heq
        simp only [orAt, List.mem_map, List.mem_singleton] at hx hy
        obtain ⟨_, _, h1⟩ := hx; rw [hy] at h1; cases h1
      · refine (List.nodup_finRange t).imp_of_mem ?_
        intro j1 j2 _ _ hne x h1 h2
        simp only [List.mem_append, List.mem_singleton] at h1 h2
        rcases h1 with h1 | rfl <;> rcases h2 with h2 | heq
        · exact hdisj_or j1.val j2.val (fun h => hne (Fin.ext h)) h1 h2
        · subst heq; simp only [orAt, List.mem_map] at h1; obtain ⟨_, _, hc⟩ := h1; cases hc
        · simp only [orAt, List.mem_map] at h2; obtain ⟨_, _, hc⟩ := h2; cases hc
        · exact hne (Sum.inr.inj heq)
    · intro x hx y hy heq
      subst heq
      simp only [List.mem_flatMap, List.mem_append, List.mem_singleton] at hx
      obtain ⟨j, _, hj⟩ := hx
      rcases hj with h1 | rfl
      · exact hdisj_or j.val t (by omega) h1 hy
      · simp only [orAt, List.mem_map] at hy; obtain ⟨_, _, hc⟩ := hy; cases hc
  have horder_mem : ∀ x : Fin E.gates.length ⊕ Fin t, x ∈ order := by
    intro x
    cases x with
    | inl k =>
      have hl := hlvl_le_t (n + t + k.val)
      simp only [order, List.mem_append, List.mem_flatMap]
      by_cases hlt : lvl (n + t + k.val) < t
      · left
        refine ⟨⟨lvl (n + t + k.val), hlt⟩, List.mem_finRange _, Or.inl ?_⟩
        simp [orAt, List.mem_finRange]
      · right
        have heq : lvl (n + t + k.val) = t := by omega
        simp [orAt, List.mem_finRange, heq]
    | inr j =>
      simp only [order, List.mem_append, List.mem_flatMap]
      left
      exact ⟨j, List.mem_finRange _, Or.inr (by simp)⟩
  have horder_len : order.length = E.gates.length + t := by
    have h1 := List.toFinset_card_of_nodup horder_nodup
    have h2 : order.toFinset = Finset.univ := by ext x; simp [horder_mem]
    rw [h2, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
    exact h1.symm

  let pos (x : Fin E.gates.length ⊕ Fin t) : ℕ := order.idxOf x
  have hpos_lt : ∀ x, pos x < order.length := fun x => List.idxOf_lt_length_of_mem (horder_mem x)
  have horder_get_pos : ∀ x, order[pos x]'(hpos_lt x) = x := fun x => List.getElem_idxOf (hpos_lt x)
  have hpos_get : ∀ (idx : ℕ) (hidx : idx < order.length), pos (order[idx]'hidx) = idx := fun idx hidx => by
    dsimp [pos]
    exact List.Nodup.idxOf_getElem horder_nodup idx hidx

  let itemKey : Fin E.gates.length ⊕ Fin t → ℕ × ℕ × ℕ
    | Sum.inl k => (lvl (n + t + k.val), 0, k.val)
    | Sum.inr j => (j.val, 1, 0)
  let keyLt (a b : ℕ × ℕ × ℕ) : Prop :=
    a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))
  have hkeyLt_irrefl : ∀ a, ¬keyLt a a := by intro a h; simp [keyLt] at h
  have hkeyLt_asym : ∀ a b, keyLt a b → ¬keyLt b a := by
    intro a b h1 h2; rcases h1 with h | ⟨e, h | ⟨e2, h⟩⟩ <;> rcases h2 with h' | ⟨e', h' | ⟨e2', h'⟩⟩ <;> omega
  have horder_sorted : order.Pairwise (fun x y => keyLt (itemKey x) (itemKey y)) := by
    have horAt_sorted : ∀ lev, (orAt lev).Pairwise (fun x y => keyLt (itemKey x) (itemKey y)) := by
      intro lev
      rw [List.pairwise_map]
      have hfin : (List.finRange E.gates.length).Pairwise (fun a b : Fin E.gates.length => a.val < b.val) := by
        rw [List.pairwise_iff_getElem]
        intro i1 i2 h1 h2 hlt
        simp [hlt]
      refine (hfin.filter _).imp_of_mem ?_
      intro a b ha hb hlt
      have ha' := decide_eq_true_eq.mp (List.mem_filter.mp ha).2
      have hb' := decide_eq_true_eq.mp (List.mem_filter.mp hb).2
      exact Or.inr ⟨ha'.trans hb'.symm, Or.inr ⟨rfl, hlt⟩⟩
    rw [List.pairwise_append]
    refine ⟨?_, horAt_sorted t, ?_⟩
    · rw [List.pairwise_flatMap]
      refine ⟨fun j _ => ?_, ?_⟩
      · rw [List.pairwise_append]
        refine ⟨horAt_sorted j.val, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
        rw [List.mem_singleton] at hy; subst hy
        simp only [orAt, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
        obtain ⟨k, ⟨_, hk⟩, rfl⟩ := hx
        exact Or.inr ⟨hk, Or.inl (by dsimp [itemKey]; omega)⟩
      · have hfin : (List.finRange t).Pairwise (fun a b : Fin t => a.val < b.val) := by
          rw [List.pairwise_iff_getElem]; intro i1 i2 h1 h2 hlt; simp [hlt]
        refine hfin.imp_of_mem ?_
        intro j1 j2 _ _ hlt x h1 y h2
        simp only [List.mem_append, List.mem_singleton] at h1 h2
        have h1_fst : (itemKey x).1 = j1.val := by
          rcases h1 with h1 | rfl
          · simp only [orAt, List.mem_map, List.mem_filter, decide_eq_true_eq] at h1
            obtain ⟨k, ⟨_, hk⟩, rfl⟩ := h1; exact hk
          · rfl
        have h2_fst : (itemKey y).1 = j2.val := by
          rcases h2 with h2 | rfl
          · simp only [orAt, List.mem_map, List.mem_filter, decide_eq_true_eq] at h2
            obtain ⟨k, ⟨_, hk⟩, rfl⟩ := h2; exact hk
          · rfl
        exact Or.inl (by omega)
    · intro x hx y hy
      simp only [List.mem_flatMap, List.mem_append, List.mem_singleton] at hx
      obtain ⟨j, _, hj⟩ := hx
      have hx_fst : (itemKey x).1 = j.val := by
        rcases hj with h1 | rfl
        · simp only [orAt, List.mem_map, List.mem_filter, decide_eq_true_eq] at h1
          obtain ⟨k, ⟨_, hk⟩, rfl⟩ := h1; exact hk
        · rfl
      simp only [orAt, List.mem_map, List.mem_filter, decide_eq_true_eq] at hy
      obtain ⟨k, ⟨_, hk⟩, rfl⟩ := hy
      have hjlt := j.isLt
      exact Or.inl (by rw [hx_fst]; dsimp [itemKey]; omega)
  have hpos_lt_of_key : ∀ x y, keyLt (itemKey x) (itemKey y) → pos x < pos y := by
    intro x y hkey
    by_contra hge
    push_neg at hge
    rcases Nat.eq_or_lt_of_le hge with heq | hlt
    · have hxy : x = y := by
        have h1 := horder_get_pos x
        have h2 := horder_get_pos y
        rw [← h1, ← h2]
        simp only [heq]
      subst hxy; exact hkeyLt_irrefl _ hkey
    · have hpw := List.pairwise_iff_getElem.mp horder_sorted (pos y) (pos x) (hpos_lt y) (hpos_lt x) hlt
      rw [horder_get_pos y, horder_get_pos x] at hpw
      exact hkeyLt_asym _ _ hkey hpw

  let N_C := n + order.length
  let mapE (u : ℕ) : ℕ :=
    if hun : u < n then u
    else if h1 : u < n + t then n + pos (Sum.inr ⟨u - n, by omega⟩)
    else if h2 : u < n + t + E.gates.length then n + pos (Sum.inl ⟨u - (n + t), by omega⟩)
    else N_C

  let translateItem (item : Fin E.gates.length ⊕ Fin t) : Gate :=
    match item with
    | Sum.inl k =>
      let g := E.gates[k.val]
      ⟨GateOp.or, (g.inputs.filter (· < n + t + k.val)).map mapE⟩
    | Sum.inr j =>
      let w := wE (Fin.natAdd m j)
      if w < n + t + E.gates.length then ⟨GateOp.not, [mapE w]⟩
      else ⟨GateOp.not, []⟩
  let C : Circuit := ⟨order.map translateItem, 0⟩
  have hC_len : C.gates.length = order.length := by simp [C]
  have hC_size : C.size ≤ s := by
    change C.gates.length ≤ s; rw [hC_len, horder_len]; exact hE_sz
  have hC_gates : ∀ g ∈ C.gates, isOr g ∨ isNot g := by
    intro g hg
    simp only [C, List.mem_map] at hg
    obtain ⟨item, _, rfl⟩ := hg
    cases item with
    | inl k =>
      left; refine ⟨rfl, ?_⟩
      rw [List.length_map]
      exact le_trans (List.length_filter_le _ _) (hE_or _ (List.getElem_mem k.isLt)).2
    | inr j =>
      right; dsimp [translateItem]
      split_ifs <;> exact ⟨rfl, by simp⟩
  have hC_not_count : C.gates.countP (fun g => @decide (isNot g) (Classical.propDecidable _)) ≤ b := by
    have haux : ∀ l : List (Fin E.gates.length ⊕ Fin t),
        (l.map translateItem).countP (fun g => @decide (isNot g) (Classical.propDecidable _)) =
        l.countP (fun item => match item with | Sum.inl _ => false | Sum.inr _ => true) := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.map_cons, List.countP_cons, ih]
        cases x with
        | inl k =>
          have hnn : ¬isNot (translateItem (Sum.inl k)) := fun h => by
            have := h.1; dsimp [translateItem] at this; cases this
          simp [hnn]
        | inr j =>
          have hn : isNot (translateItem (Sum.inr j)) := by
            dsimp [translateItem]; split_ifs <;> exact ⟨rfl, by simp⟩
          simp [hn]
    have hcount_inr : order.countP (fun item => match item with | Sum.inl _ => false | Sum.inr _ => true) = t := by
      have h1 : ∀ l : List (Fin E.gates.length ⊕ Fin t),
          l.countP (fun item => match item with | Sum.inl _ => false | Sum.inr _ => true) =
          (l.filter (fun item => match item with | Sum.inl _ => false | Sum.inr _ => true)).length :=
        fun l => List.countP_eq_length_filter
      rw [h1]
      have hnd := horder_nodup.filter (fun item => match item with | Sum.inl _ => false | Sum.inr _ => true)
      have hcard := List.toFinset_card_of_nodup hnd
      have hset : (order.filter (fun item => match item with | Sum.inl _ => false | Sum.inr _ => true)).toFinset =
          Finset.univ.image Sum.inr := by
        ext x
        simp only [List.mem_toFinset, List.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        cases x with
        | inl k => simp
        | inr j => simp [horder_mem]
      rw [hset, Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, Fintype.card_fin] at hcard
      exact hcard.symm
    change (order.map translateItem).countP _ ≤ b
    rw [haux, hcount_inr]
    exact ht

  have hmapE_lt_or : ∀ (k : Fin E.gates.length) (u : ℕ),
      u ∈ (E.gates[k.val]).inputs → u < n + t + k.val → mapE u < n + pos (Sum.inl k) := by
    intro k u hu hult
    have hlv := hlvl_gate_mono k u hu hult
    by_cases hun : u < n
    · simp only [mapE, dif_pos hun]; omega
    · by_cases hunt : u < n + t
      · simp only [mapE, dif_neg hun, dif_pos hunt]
        let j : Fin t := ⟨u - n, by omega⟩
        have hueq : u = n + j.val := by dsimp [j]; omega
        rw [hueq, hlvl_extra j] at hlv
        have hkey : keyLt (itemKey (Sum.inr j)) (itemKey (Sum.inl k)) :=
          Or.inl (by dsimp [itemKey]; omega)
        have hlt_p := hpos_lt_of_key (Sum.inr j) (Sum.inl k) hkey
        change n + pos (Sum.inr j) < n + pos (Sum.inl k)
        omega
      · simp only [mapE, dif_neg hun, dif_neg hunt, dif_pos (by omega : u < n + t + E.gates.length)]
        let k' : Fin E.gates.length := ⟨u - (n + t), by omega⟩
        have hueq : u = n + t + k'.val := by dsimp [k']; omega
        rw [hueq] at hlv
        have hklt : k'.val < k.val := by dsimp [k']; omega
        have hkey : keyLt (itemKey (Sum.inl k')) (itemKey (Sum.inl k)) := by
          rcases Nat.lt_or_eq_of_le hlv with hlt | heq
          · exact Or.inl hlt
          · exact Or.inr ⟨heq, Or.inr ⟨rfl, hklt⟩⟩
        have hlt_p := hpos_lt_of_key (Sum.inl k') (Sum.inl k) hkey
        change n + pos (Sum.inl k') < n + pos (Sum.inl k)
        omega
  have hmapE_lt_not : ∀ (j : Fin t), wE (Fin.natAdd m j) < n + t + E.gates.length →
      mapE (wE (Fin.natAdd m j)) < n + pos (Sum.inr j) := by
    intro j hwlt
    set u := wE (Fin.natAdd m j)
    have hlv : lvl u ≤ j.val := hlvl_not_in j
    by_cases hun : u < n
    · simp only [mapE, dif_pos hun]; omega
    · by_cases hunt : u < n + t
      · simp only [mapE, dif_neg hun, dif_pos hunt]
        let i : Fin t := ⟨u - n, by omega⟩
        have hueq : u = n + i.val := by dsimp [i]; omega
        rw [hueq, hlvl_extra i] at hlv
        have hkey : keyLt (itemKey (Sum.inr i)) (itemKey (Sum.inr j)) :=
          Or.inl (by dsimp [itemKey]; omega)
        have hlt_p := hpos_lt_of_key (Sum.inr i) (Sum.inr j) hkey
        change n + pos (Sum.inr i) < n + pos (Sum.inr j)
        omega
      · simp only [mapE, dif_neg hun, dif_neg hunt, dif_pos hwlt]
        let k' : Fin E.gates.length := ⟨u - (n + t), by omega⟩
        have hueq : u = n + t + k'.val := by dsimp [k']; omega
        rw [hueq] at hlv
        have hkey : keyLt (itemKey (Sum.inl k')) (itemKey (Sum.inr j)) := by
          rcases Nat.lt_or_eq_of_le hlv with hlt | heq
          · exact Or.inl hlt
          · exact Or.inr ⟨heq, Or.inl (by dsimp [itemKey]; omega)⟩
        have hlt_p := hpos_lt_of_key (Sum.inl k') (Sum.inr j) hkey
        change n + pos (Sum.inl k') < n + pos (Sum.inr j)
        omega

  let vIn (x : Fin n) : Fin (n + t) → Bool := fun u =>
    if hu : u.val < n then decide (u.val = x.val)
    else z x ⟨u.val - n, by omega⟩
  have hsim_idx : ∀ (x : Fin n) (idx : ℕ) (hidx : idx < order.length),
      (C.wires (oneHot n x)).getD (n + idx) false =
        match order[idx]'hidx with
        | Sum.inl k => (E.wires (List.ofFn (vIn x))).getD (n + t + k.val) false
        | Sum.inr j => z x j := by
    intro x idx
    induction idx using Nat.strong_induction_on with
    | ind idx ih =>
      intro hidx

      have hsim_u : ∀ u, u < n + t + E.gates.length → mapE u < n + idx →
          (C.wires (oneHot n x)).getD (mapE u) false = (E.wires (List.ofFn (vIn x))).getD u false := by
        intro u hult hmlt
        by_cases hun : u < n
        · simp only [mapE, dif_pos hun]
          rw [wires_getD_input C _ u (by rw [oneHot_length]; exact hun), oneHot_getD,
            wires_getD_input E _ u (by simp; omega), getD_ofFn _ u (by omega)]
          simp [vIn, hun]
        · by_cases hunt : u < n + t
          · simp only [mapE, dif_neg hun, dif_pos hunt] at hmlt ⊢
            let j : Fin t := ⟨u - n, by omega⟩
            have hmlt' : n + pos (Sum.inr j) < n + idx := hmlt
            have hidx' := hpos_lt (Sum.inr j)
            change (C.wires (oneHot n x)).getD (n + pos (Sum.inr j)) false = _
            rw [ih (pos (Sum.inr j)) (by omega) hidx', horder_get_pos (Sum.inr j)]
            dsimp only
            rw [wires_getD_input E _ u (by simp; omega), getD_ofFn _ u (by omega)]
            simp [vIn, hun, j]
          · simp only [mapE, dif_neg hun, dif_neg hunt, dif_pos hult] at hmlt ⊢
            let k : Fin E.gates.length := ⟨u - (n + t), by omega⟩
            have hmlt' : n + pos (Sum.inl k) < n + idx := hmlt
            have hidx' := hpos_lt (Sum.inl k)
            change (C.wires (oneHot n x)).getD (n + pos (Sum.inl k)) false = _
            rw [ih (pos (Sum.inl k)) (by omega) hidx', horder_get_pos (Sum.inl k)]
            dsimp only
            have hueq : n + t + k.val = u := by dsimp [k]; omega
            rw [hueq]
      have hCg := wires_getD_gate C (oneHot n x) idx (by rw [hC_len]; exact hidx)
      simp only [oneHot_length] at hCg
      rw [hCg]
      have hgate_eq : C.gates[idx]'(by rw [hC_len]; exact hidx) = translateItem (order[idx]'hidx) := by
        simp [C]
      rw [hgate_eq]
      cases hitem : order[idx]'hidx with
      | inl k =>
        have hpos_eq : pos (Sum.inl k) = idx := by rw [← hitem]; exact hpos_get idx hidx
        dsimp [translateItem]
        rw [GateOp.eval]
        have hEg := wires_getD_gate E (List.ofFn (vIn x)) k.val k.isLt
        simp only [List.length_ofFn, (hE_or _ (List.getElem_mem k.isLt)).1, GateOp.eval] at hEg
        rw [hEg]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, List.mem_map, id_eq]
        constructor
        · rintro ⟨_, ⟨w, hw, rfl⟩, htrue⟩
          obtain ⟨u, hu, rfl⟩ := hw
          rw [List.mem_filter, decide_eq_true_eq] at hu
          have hmlt : mapE u < n + idx := by rw [← hpos_eq]; exact hmapE_lt_or k u hu.1 hu.2
          rw [if_pos hmlt, hsim_u u (by omega) hmlt] at htrue
          exact ⟨true, ⟨u, hu.1, by rw [if_pos hu.2]; exact htrue⟩, rfl⟩
        · rintro ⟨_, ⟨u, hu, htrue⟩, rfl⟩
          by_cases hult : u < n + t + k.val
          · rw [if_pos hult] at htrue
            have hmlt : mapE u < n + idx := by rw [← hpos_eq]; exact hmapE_lt_or k u hu hult
            refine ⟨true, ⟨mapE u, ⟨u, List.mem_filter.mpr ⟨hu, decide_eq_true hult⟩, rfl⟩, ?_⟩, rfl⟩
            rw [if_pos hmlt, hsim_u u (by omega) hmlt]
            exact htrue
          · rw [if_neg hult] at htrue; cases htrue
      | inr j =>
        have hpos_eq : pos (Sum.inr j) = idx := by rw [← hitem]; exact hpos_get idx hidx
        dsimp only
        rw [hz_rec x j]
        have hlin := or_circuit_linear (n + t) E hE_or (vIn x) (wE (Fin.natAdd m j))
        have hE_eq : (E.wires (List.ofFn (vIn x))).getD (wE (Fin.natAdd m j)) false =
            (R (Fin.castAdd t x) (Fin.natAdd m j) ||
              decide (∃ i : Fin t, i < j ∧ z x i = true ∧ R (Fin.natAdd n i) (Fin.natAdd m j) = true)) := by
          rw [hlin]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, Bool.or_eq_true]
          constructor
          · rintro ⟨u, hvu, hEu⟩
            rw [hwE (Fin.natAdd m j) u] at hEu
            dsimp only at hEu
            by_cases hun : u.val < n
            · simp only [vIn, dif_pos hun, decide_eq_true_eq] at hvu
              left
              have hueq : u = Fin.castAdd t x := Fin.ext hvu
              subst hueq; exact hEu
            · simp only [vIn, dif_neg hun] at hvu
              let i : Fin t := ⟨u.val - n, by omega⟩
              have hueq : u = Fin.natAdd n i := Fin.ext (by dsimp [i, Fin.natAdd]; omega)
              rw [hueq] at hEu
              have hilt : i < j := by
                by_contra hge
                have hfalse := hR_causal i j (Nat.le_of_not_lt hge)
                rw [hfalse] at hEu; exact Bool.false_ne_true hEu
              exact Or.inr ⟨i, hilt, hvu, hEu⟩
          · rintro (hxR | ⟨i, _, hzi, hiR⟩)
            · exact ⟨Fin.castAdd t x, by simp [vIn], by rw [hwE]; exact hxR⟩
            · exact ⟨Fin.natAdd n i, by simp [vIn, Fin.natAdd, show ¬(n + i.val < n) by omega, hzi], by rw [hwE]; exact hiR⟩
        rw [← hE_eq]
        dsimp [translateItem]
        split_ifs with hwlt
        · rw [GateOp.eval]
          simp only [List.map_cons, List.map_nil, List.headD_cons]
          have hmlt : mapE (wE (Fin.natAdd m j)) < n + idx := by
            rw [← hpos_eq]; exact hmapE_lt_not j hwlt
          rw [if_pos hmlt, hsim_u _ hwlt hmlt]
        · rw [GateOp.eval]
          simp only [List.map_nil, List.headD_nil]
          rw [List.getD_eq_default _ _ (by rw [wires_length, List.length_ofFn]; omega)]

  have hC_hits : hits n m M C := by
    intro y
    refine ⟨mapE (wE (Fin.castAdd t y)), fun x => ?_⟩
    rw [hM_rec x y]
    have hlin := or_circuit_linear (n + t) E hE_or (vIn x) (wE (Fin.castAdd t y))
    have hE_eq : (E.wires (List.ofFn (vIn x))).getD (wE (Fin.castAdd t y)) false =
        (R (Fin.castAdd t x) (Fin.castAdd t y) ||
          decide (∃ i : Fin t, z x i = true ∧ R (Fin.natAdd n i) (Fin.castAdd t y) = true)) := by
      rw [hlin]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.or_eq_true]
      constructor
      · rintro ⟨u, hvu, hEu⟩
        rw [hwE (Fin.castAdd t y) u] at hEu
        by_cases hun : u.val < n
        · simp only [vIn, dif_pos hun, decide_eq_true_eq] at hvu
          left
          have hueq : u = Fin.castAdd t x := Fin.ext hvu
          subst hueq; exact hEu
        · simp only [vIn, dif_neg hun] at hvu
          let i : Fin t := ⟨u.val - n, by omega⟩
          have hueq : u = Fin.natAdd n i := Fin.ext (by dsimp [i, Fin.natAdd]; omega)
          rw [hueq] at hEu
          exact Or.inr ⟨i, hvu, hEu⟩
      · rintro (hxR | ⟨i, hzi, hiR⟩)
        · exact ⟨Fin.castAdd t x, by simp [vIn], by rw [hwE]; exact hxR⟩
        · exact ⟨Fin.natAdd n i, by simp [vIn, Fin.natAdd, show ¬(n + i.val < n) by omega, hzi], by rw [hwE]; exact hiR⟩
    rw [← hE_eq]
    set u := wE (Fin.castAdd t y)
    by_cases hun : u < n
    · simp only [mapE, dif_pos hun]
      rw [wires_getD_input C _ u (by rw [oneHot_length]; exact hun), oneHot_getD,
        wires_getD_input E _ u (by simp; omega), getD_ofFn _ u (by omega)]
      simp [vIn, hun]
    · by_cases hunt : u < n + t
      · simp only [mapE, dif_neg hun, dif_pos hunt]
        let j : Fin t := ⟨u - n, by omega⟩
        rw [hsim_idx x (pos (Sum.inr j)) (hpos_lt (Sum.inr j)), horder_get_pos (Sum.inr j),
          wires_getD_input E _ u (by simp; omega), getD_ofFn _ u (by omega)]
        simp [vIn, hun, j]
      · by_cases huE : u < n + t + E.gates.length
        · simp only [mapE, dif_neg hun, dif_neg hunt, dif_pos huE]
          let k : Fin E.gates.length := ⟨u - (n + t), by omega⟩
          change (C.wires (oneHot n x)).getD (n + pos (Sum.inl k)) false = _
          rw [hsim_idx x (pos (Sum.inl k)) (hpos_lt (Sum.inl k)), horder_get_pos (Sum.inl k)]
          dsimp only
          have hueq : n + t + k.val = u := by dsimp [k]; omega
          rw [hueq]
        · simp only [mapE, dif_neg hun, dif_neg hunt, dif_neg huE]
          rw [List.getD_eq_default _ _ (by rw [wires_length, oneHot_length, hC_len]),
            List.getD_eq_default _ _ (by rw [wires_length, List.length_ofFn]; omega)]
  exact ⟨C, hC_hits, hC_gates, hC_size, hC_not_count⟩

end PEqualNP.Outside.L_lib_756_aux

theorem PEqualNP.Outside.L_lib_756 : ∀ (n m : ℕ) (M : Fin n → Fin m → Bool) (b s : ℕ),
  let hits := fun (p q : ℕ) (A : Fin p → Fin q → Bool)
      (E : PEqualNP.CircuitLowerBounds.Circuit) =>
    ∀ y : Fin q, ∃ w : ℕ, ∀ x : Fin p,
      (E.wires (List.ofFn (fun h : Fin p => decide (h = x)))).getD w false = A x y
  let isOr := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2
  let isNot := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length ≤ 1
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, hits n m M C ∧
    (∀ g ∈ C.gates, isOr g ∨ isNot g) ∧ C.size ≤ s ∧
    C.gates.countP (fun g => @decide (isNot g) (Classical.propDecidable _)) ≤ b) ↔
  ∃ t : ℕ, t ≤ b ∧ ∃ (R : Fin (n+t) → Fin (m+t) → Bool) (z : Fin n → Fin t → Bool),
    (∀ i j : Fin t, j ≤ i → R (Fin.natAdd n i) (Fin.natAdd m j) = false) ∧
    (∀ (x : Fin n) (j : Fin t), z x j =
      !(R (Fin.castAdd t x) (Fin.natAdd m j) ||
        decide (∃ i : Fin t, i < j ∧ z x i = true ∧ R (Fin.natAdd n i) (Fin.natAdd m j) = true))) ∧
    (∀ (x : Fin n) (y : Fin m), M x y =
      (R (Fin.castAdd t x) (Fin.castAdd t y) ||
        decide (∃ i : Fin t, z x i = true ∧ R (Fin.natAdd n i) (Fin.castAdd t y) = true))) ∧
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      hits (m+t) (n+t) (fun y x => R x y) D ∧ (∀ g ∈ D.gates, isOr g) ∧
      D.size + ((Finset.univ : Finset (Fin (n+t))).filter (fun u => ∃ v, R u v = true)).card + t ≤
        s + ((Finset.univ : Finset (Fin (m+t))).filter (fun v => ∃ u, R u v = true)).card := by
  intro n m M b s
  constructor
  · rintro ⟨C, hhits, hgates, hsz, hb⟩
    exact PEqualNP.Outside.L_lib_756_aux.forward_dir n m M b s C hhits hgates hsz hb
  · rintro ⟨t, ht, R, z, hRc, hzr, hMr, D, hDh, hDo, hDb⟩
    exact PEqualNP.Outside.L_lib_756_aux.backward_dir n m M b s t ht R z hRc hzr hMr D hDh hDo hDb
